// Pure, decoupled real-time Opus [D]: tuple scanner & Beat 0 / post-stream reconciliation helpers.

export type RawDialogueTuple = [number, ...unknown[]];

export interface DispatchedBeatRecord {
  beatIndex: number;
  uid: number;
  sig: string;
  usedCelerisEnricher: boolean;
}

export interface TurnBeatDispatcherState {
  nextBeatIndex: number;
  dispatched: DispatchedBeatRecord[];
  dispatchedSigs: Set<string>;
}

const FORBIDDEN_TUPLE_TAGS_RX = /\[(?:TURN_JSON|GAME_STATE_JSON|SOL_STATE_JSON|REFEREE_TAG|REFEREE_HEADER|NPC|NPC_DELTA|OPUS_NPC|BGM)\]/i;

export function computeBeatContentSig(uidVal: number | string, textVal: string): string {
  const normWords = String(textVal || '')
    .replace(/<[^>]+>|\[[^\]]*\]|\{[^{}]*\}/g, ' ')
    .toLowerCase()
    .replace(/[^a-z0-9']+/g, ' ')
    .trim();
  return `${Number(uidVal) || 1000}__${normWords}`;
}

function extractCleanOrThoughtText(rawSpeech: string, rawThought = ''): string {
  const s = String(rawSpeech || '').trim();
  const t = String(rawThought || '').trim();
  const strippedSpeech = s.replace(/\{([^{}]+)\}/g, ' ').replace(/\s{2,}/g, ' ').trim();
  if (strippedSpeech) return strippedSpeech;
  if (t) return t;
  const innerMatches = [...s.matchAll(/\{([^{}]+)\}/g)].map(m => m[1].trim()).filter(Boolean);
  return innerMatches.join(' ').trim();
}

export function extractTuplePrimaryText(tuple: unknown[]): string {
  if (!Array.isArray(tuple) || tuple.length < 2) return '';
  if (tuple.length >= 4) {
    return extractCleanOrThoughtText(String(tuple[2] ?? ''), String(tuple[3] ?? ''));
  }
  if (tuple.length === 3 && typeof tuple[2] === 'string') {
    return extractCleanOrThoughtText(tuple[2]);
  }
  return extractCleanOrThoughtText(String(tuple[1] ?? ''));
}

export function shouldEnrichBeatWithCeleris(uid: number): boolean {
  // Narrator (UID 1000) beats — both Beat 0 (GPT-OSS) and short Opus beats — never wait for Celeris micro-enrichment.
  return Number(uid) >= 1002;
}

export function clampShortOpusNarration(rawText: string, maxWords = 16, maxChars = 140): string {
  const clean = String(rawText || '').replace(/\s+/g, ' ').trim();
  if (!clean) return '';

  // Keep only the first crisp sentence so Opus mid-scene narrations stay very short.
  let firstSentence = clean;
  const protectedClean = clean
    .replace(/\b(Mr|Mrs|Ms|Dr|St|Lv|No)\./gi, '$1__DOT__')
    .replace(/\.\.\./g, '__ELLIPSIS__');
  const sentSplit = protectedClean.match(/^(.+?[.!?])(?=\s+[A-Z0-9"'(\[])/);
  if (sentSplit && sentSplit[1]) {
    firstSentence = sentSplit[1]
      .replace(/__DOT__/g, '.')
      .replace(/__ELLIPSIS__/g, '...')
      .trim();
  }

  const words = firstSentence.split(/\s+/).filter(Boolean);
  let shortened = words.length > maxWords ? words.slice(0, maxWords).join(' ') : firstSentence;

  if (shortened.length > maxChars) {
    const sliced = shortened.slice(0, maxChars);
    const lastSpace = sliced.lastIndexOf(' ');
    shortened = (lastSpace > 24 ? sliced.slice(0, lastSpace) : sliced).trim();
  }

  shortened = shortened.replace(/[,;:\-—]+$/g, '').trim();
  if (shortened && !/[.!?…]$/.test(shortened)) {
    shortened += '.';
  }
  return shortened;
}

export function isNearDuplicateBeat0Narration(beat0Text: string, candidateText: string): boolean {
  const toWords = (s: string) =>
    String(s || '')
      .toLowerCase()
      .replace(/[^a-z0-9'\s]+/g, ' ')
      .split(/\s+/)
      .filter(Boolean);
  const b0 = toWords(beat0Text);
  const cand = toWords(candidateText);
  if (b0.length === 0 || cand.length === 0) return false;
  if (cand.join(' ') === b0.join(' ')) return true;
  if (cand.length >= 4 && b0.slice(0, 4).join(' ') === cand.slice(0, 4).join(' ')) return true;
  const b0Set = new Set(b0);
  const overlap = cand.filter(w => b0Set.has(w)).length;
  return cand.length >= 4 && (overlap / cand.length) >= 0.8;
}

export function extractCompleteJsonStringField(rawPartial: string, fieldName: string): string | null {
  let src = String(rawPartial || '');
  // Strip completed <think>...</think> blocks cleanly; if inside unclosed <think>, wait for </think>.
  const openThink = src.indexOf('<think>');
  if (openThink !== -1) {
    const closeThink = src.indexOf('</think>', openThink + 7);
    if (closeThink === -1) return null;
    src = src.slice(0, openThink) + src.slice(closeThink + 8);
  }
  const objStart = src.indexOf('{');
  if (objStart === -1) return null;

  let i = objStart;
  const len = src.length;
  let depth = 0;

  while (i < len) {
    const ch = src[i];
    if (ch === '{' || ch === '[') {
      depth++;
      i++;
      continue;
    }
    if (ch === '}' || ch === ']') {
      depth--;
      i++;
      if (depth <= 0) break;
      continue;
    }
    if (ch === '"') {
      const strStart = i;
      i++;
      let esc = false;
      let strEnd = -1;
      while (i < len) {
        const c = src[i];
        if (esc) { esc = false; i++; continue; }
        if (c === '\\') { esc = true; i++; continue; }
        if (c === '"') { strEnd = i; i++; break; }
        i++;
      }
      if (strEnd === -1) return null; // Current string literal is still streaming!

      // Check if this string at top-level object depth 1 is our target JSON property key
      let k = i;
      while (k < len && /\s/.test(src[k])) k++;
      if (depth === 1 && k < len && src[k] === ':') {
        let keyName = '';
        try { keyName = JSON.parse(src.slice(strStart, strEnd + 1)); } catch {}
        if (keyName === fieldName) {
          k++;
          while (k < len && /\s/.test(src[k])) k++;
          if (k >= len || src[k] !== '"') return null;
          const valStart = k;
          k++;
          let vEsc = false;
          let valEnd = -1;
          while (k < len) {
            const vc = src[k];
            if (vEsc) { vEsc = false; k++; continue; }
            if (vc === '\\') { vEsc = true; k++; continue; }
            if (vc === '"') { valEnd = k; break; }
            k++;
          }
          if (valEnd === -1) return null; // Value string still streaming!
          try {
            return String(JSON.parse(src.slice(valStart, valEnd + 1)));
          } catch {
            return null;
          }
        }
      }
      continue;
    }
    i++;
  }
  return null;
}

export function isValidAuthorizedMidStreamNpcTuple(
  tuple: unknown,
  allowedSpeakerUids: Iterable<number | string>
): tuple is RawDialogueTuple {
  if (!Array.isArray(tuple) || tuple.length < 2) return false;
  const uid = Number(tuple[0]);
  if (!Number.isInteger(uid) || uid === 1001) return false;

  // Accept short interleaved [1000, "..."] narrator beats from Opus mid-stream.
  if (uid === 1000) {
    const rawNarration = tuple.length >= 3 && typeof tuple[2] === 'string'
      ? tuple[2]
      : (typeof tuple[1] === 'string' ? tuple[1] : '');
    return Boolean(rawNarration.trim()) && rawNarration.length <= 600 && !FORBIDDEN_TUPLE_TAGS_RX.test(rawNarration);
  }

  const allowed = new Set<number>();
  for (const raw of allowedSpeakerUids) {
    const n = Number(raw);
    if (Number.isInteger(n)) allowed.add(n);
  }
  if (!allowed.has(uid)) return false;

  if (tuple.length === 2) {
    const speech = typeof tuple[1] === 'string' ? tuple[1] : '';
    return Boolean(speech.trim()) && speech.length <= 2400 && !FORBIDDEN_TUPLE_TAGS_RX.test(speech);
  }

  const emoji = typeof tuple[1] === 'string' ? tuple[1].trim() : '';
  const speech = typeof tuple[2] === 'string' ? tuple[2] : '';
  const thought = tuple[3] == null ? '' : (typeof tuple[3] === 'string' ? tuple[3] : '');
  if (emoji.length > 64 || speech.length > 2400 || thought.length > 1600) return false;
  if (FORBIDDEN_TUPLE_TAGS_RX.test(emoji) || FORBIDDEN_TUPLE_TAGS_RX.test(speech) || FORBIDDEN_TUPLE_TAGS_RX.test(thought)) {
    return false;
  }
  return Boolean(speech.trim() || thought.trim());
}

export const isValidAuthorizedMidStreamTuple = isValidAuthorizedMidStreamNpcTuple;

export function parseRawTupleSlice(rawSlice: string): RawDialogueTuple | null {
  try {
    const parsed = JSON.parse(rawSlice);
    if (Array.isArray(parsed) && parsed.length >= 2) {
      return parsed as RawDialogueTuple;
    }
  } catch {
    // Fallback for minor unescaped quotes inside streamed dialogue strings
    const m4 = rawSlice.match(/^\[\s*(\d{4})\s*,\s*"([^"]*)"\s*,\s*"([\s\S]*?)"\s*,\s*"([\s\S]*)"\s*\]$/);
    if (m4) {
      return [Number(m4[1]), m4[2], m4[3], m4[4]];
    }
    const m = rawSlice.match(/^\[\s*(\d{4})\s*,\s*(?:"([^"]*)"\s*,\s*)?"([\s\S]*)"\s*\]$/);
    if (m) {
      return m[2] !== undefined ? [Number(m[1]), m[2], m[3]] : [Number(m[1]), m[3]];
    }
  }
  return null;
}

export class IncrementalOpusTupleScanner {
  private buffer = '';
  private outerBracketIdx = -1;
  private cursor = 0;
  public dArrayClosed = false;

  appendChunk(chunk: string): RawDialogueTuple[] {
    if (!chunk || this.dArrayClosed) return [];
    this.buffer += chunk;
    return this.scan();
  }

  getBuffer(): string {
    return this.buffer;
  }

  scan(): RawDialogueTuple[] {
    if (this.dArrayClosed) return [];

    if (this.outerBracketIdx === -1) {
      let searchFrom = 0;
      const openThink = this.buffer.indexOf('<think>');
      if (openThink !== -1) {
        const closeThink = this.buffer.indexOf('</think>', openThink + 7);
        if (closeThink === -1) return [];
        searchFrom = closeThink + 8;
      }

      const tail = this.buffer.slice(searchFrom);
      const dMatch = tail.match(/\[D\]\s*:/i);
      if (dMatch && dMatch.index !== undefined) {
        const afterD = searchFrom + dMatch.index + dMatch[0].length;
        const bracketIdx = this.buffer.indexOf('[', afterD);
        if (bracketIdx === -1) return [];
        this.outerBracketIdx = bracketIdx;
        this.cursor = bracketIdx + 1;
      } else {
        const bareMatch = tail.match(/^\s*(?:```(?:json|text)?\s*)?(\[\[)/i);
        if (!bareMatch || bareMatch.index === undefined) return [];
        const bracketIdx = this.buffer.indexOf('[[', searchFrom + bareMatch.index);
        if (bracketIdx === -1) return [];
        this.outerBracketIdx = bracketIdx;
        this.cursor = bracketIdx + 1;
      }
    }

    const completed: RawDialogueTuple[] = [];
    const len = this.buffer.length;

    while (this.cursor < len) {
      while (this.cursor < len && /[\s,]/.test(this.buffer[this.cursor])) {
        this.cursor++;
      }
      if (this.cursor >= len) break;

      if (this.buffer[this.cursor] === ']') {
        this.dArrayClosed = true;
        this.cursor++;
        break;
      }

      if (this.buffer[this.cursor] !== '[') {
        this.cursor++;
        continue;
      }

      const tupleStart = this.cursor;
      let depth = 0;
      let inStr = false;
      let esc = false;
      let tupleEnd = -1;

      for (let j = tupleStart; j < len; j++) {
        const ch = this.buffer[j];
        if (esc) {
          esc = false;
          continue;
        }
        if (ch === '\\') {
          esc = true;
          continue;
        }
        if (ch === '"') {
          inStr = !inStr;
          continue;
        }
        if (!inStr) {
          if (ch === '[') depth++;
          else if (ch === ']') {
            depth--;
            if (depth === 0) {
              tupleEnd = j;
              break;
            }
          }
        }
      }

      if (tupleEnd === -1) break;

      const rawSlice = this.buffer.slice(tupleStart, tupleEnd + 1);
      this.cursor = tupleEnd + 1;
      const parsed = parseRawTupleSlice(rawSlice);
      if (parsed) {
        completed.push(parsed);
      }
    }

    return completed;
  }
}

export function createTurnBeatDispatcherState(): TurnBeatDispatcherState {
  return {
    nextBeatIndex: 0,
    dispatched: [],
    dispatchedSigs: new Set<string>()
  };
}

export function recordDispatchedBeat(
  state: TurnBeatDispatcherState,
  uid: number,
  textOrThought: string
): DispatchedBeatRecord {
  const sig = computeBeatContentSig(uid, textOrThought);
  const record: DispatchedBeatRecord = {
    beatIndex: state.nextBeatIndex++,
    uid: Number(uid) || 1000,
    sig,
    usedCelerisEnricher: shouldEnrichBeatWithCeleris(uid)
  };
  state.dispatched.push(record);
  state.dispatchedSigs.add(sig);
  return record;
}

export function findMissingPostStreamTuples(
  state: TurnBeatDispatcherState,
  finalTuples: RawDialogueTuple[]
): RawDialogueTuple[] {
  const remainingCountBySig = new Map<string, number>();
  for (const rec of state.dispatched) {
    remainingCountBySig.set(rec.sig, (remainingCountBySig.get(rec.sig) || 0) + 1);
  }

  const missing: RawDialogueTuple[] = [];
  for (const tuple of finalTuples) {
    if (!Array.isArray(tuple) || tuple.length < 2) continue;
    const uid = Number(tuple[0]);
    if (uid === 1001) continue;
    const sig = computeBeatContentSig(uid, extractTuplePrimaryText(tuple));
    const seenCount = remainingCountBySig.get(sig) || 0;
    if (seenCount > 0) {
      remainingCountBySig.set(sig, seenCount - 1);
    } else {
      missing.push(tuple);
    }
  }
  return missing;
}

function normalizeTupleElement(item: unknown): RawDialogueTuple | null {
  if (Array.isArray(item)) {
    if (item.length === 0) return null;
    if (item.length === 1 && Array.isArray(item[0])) {
      return normalizeTupleElement(item[0]);
    }
    if (item.length < 2) return null;
    const uid = Number(item[0]);
    if (!Number.isInteger(uid)) return null;
    return item as RawDialogueTuple;
  }
  if (item && typeof item === 'object') {
    const obj = item as Record<string, unknown>;
    const rawUid = Number(obj.uid ?? obj.id ?? (obj.type === 'narration' ? 1000 : NaN));
    if (!Number.isInteger(rawUid)) return null;
    const text = String(obj.text ?? obj.dialogue ?? '').trim();
    const emoji = typeof obj.emoji === 'string' ? obj.emoji.trim() : '';
    const thought = String(obj.inner_thought ?? obj.thought ?? '').trim();
    if (rawUid === 1000) {
      return text ? [1000, text] : null;
    }
    if (!text && !thought) return null;
    if (thought) return [rawUid, emoji || '🙂', text, thought];
    return emoji ? [rawUid, emoji, text] : [rawUid, text];
  }
  return null;
}

function coerceParsedJsonToTuples(parsed: unknown): RawDialogueTuple[] | null {
  if (!Array.isArray(parsed)) return null;
  if (parsed.length === 0) return [];

  // 1D single tuple case: [1002, "😅", "Text"]
  if (!Array.isArray(parsed[0]) && typeof parsed[0] !== 'object' && Number.isInteger(Number(parsed[0]))) {
    const single = normalizeTupleElement(parsed);
    return single ? [single] : null;
  }

  // Accidental extra nesting: [[[1002, ...], ...]]
  let rows: unknown[] = parsed;
  if (
    rows.length === 1 &&
    Array.isArray(rows[0]) &&
    rows[0].length > 0 &&
    (Array.isArray(rows[0][0]) || (rows[0][0] && typeof rows[0][0] === 'object'))
  ) {
    rows = rows[0] as unknown[];
  }

  const out: RawDialogueTuple[] = [];
  for (const row of rows) {
    if (row == null || (Array.isArray(row) && row.length === 0)) continue;
    const norm = normalizeTupleElement(row);
    if (!norm) return null; // Signal caller to try scanner/line-recovery instead
    out.push(norm);
  }
  return out;
}

export function extractOpusDialogueTuples(rawText: string): RawDialogueTuple[] | null {
  let cleaned = String(rawText || '')
    .replace(/<think>[\s\S]*?<\/think>/gi, '')
    .trim();
  if (!cleaned) return null;

  if (cleaned.startsWith('```')) {
    cleaned = cleaned.replace(/^```(?:json|text)?[ \t]*\r?\n?/i, '').replace(/\r?\n?```[ \t]*$/i, '').trim();
  }

  const dTagIdx = cleaned.search(/\[D\]\s*:/i);
  const candidate = dTagIdx !== -1
    ? cleaned.slice(dTagIdx).replace(/^\[D\]\s*:\s*/i, '').trim()
    : cleaned;

  // 1. Direct JSON parse (plus trailing-comma repair)
  const jsonCandidates = [
    candidate,
    candidate.replace(/,\s*([\]}])/g, '$1')
  ];
  for (const jc of jsonCandidates) {
    try {
      const parsed = JSON.parse(jc);
      const coerced = coerceParsedJsonToTuples(parsed);
      if (coerced !== null) return coerced;
    } catch {}
  }

  // 2. Comma-separated 1D tuples without outer brackets: [1002, ...], [1000, ...]
  if (/^\[\s*\d{3,4}\s*,/.test(candidate)) {
    const wrapped = `[${candidate.replace(/,\s*$/, '')}]`;
    try {
      const parsed = JSON.parse(wrapped);
      const coerced = coerceParsedJsonToTuples(parsed);
      if (coerced !== null) return coerced;
    } catch {}
    const wrapScanner = new IncrementalOpusTupleScanner();
    const scanned = wrapScanner.appendChunk(`[D]: ${wrapped}`);
    if (scanned.length > 0) return scanned;
  }

  // 3. Incremental scanner recovery (handles missing closing ']', unescaped inner quotes, trailing text)
  const scanner = new IncrementalOpusTupleScanner();
  const scannerInput = dTagIdx !== -1 ? cleaned.slice(dTagIdx) : (candidate.startsWith('[[') ? `[D]: ${candidate}` : cleaned);
  const scanned = scanner.appendChunk(scannerInput).map(normalizeTupleElement).filter((t): t is RawDialogueTuple => t !== null);
  if (scanned.length > 0) {
    return scanned;
  }
  if (scanner.dArrayClosed) {
    return [];
  }

  // 4. Last-chance balanced slice scan inside candidate
  const firstBracket = candidate.indexOf('[');
  if (firstBracket !== -1) {
    const tail = candidate.slice(firstBracket);
    if (/^\[\s*\d{3,4}\s*,/.test(tail)) {
      const wrapScanner = new IncrementalOpusTupleScanner();
      const s = wrapScanner.appendChunk(`[D]: [${tail}`).map(normalizeTupleElement).filter((t): t is RawDialogueTuple => t !== null);
      if (s.length > 0) return s;
    }
  }

  return null;
}

