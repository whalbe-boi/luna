import test from 'node:test';
import assert from 'node:assert/strict';
import {
  IncrementalOpusTupleScanner,
  clampShortOpusNarration,
  computeBeatContentSig,
  createTurnBeatDispatcherState,
  extractCompleteJsonStringField,
  extractOpusDialogueTuples,
  findMissingPostStreamTuples,
  isNearDuplicateBeat0Narration,
  isValidAuthorizedMidStreamNpcTuple,
  recordDispatchedBeat,
  shouldEnrichBeatWithCeleris,
  type RawDialogueTuple
} from './opusBeatStream.ts';

test('Narrator (uid 1000 — GPT-OSS Beat 0 and short Opus beats) never triggers Celeris micro-enrichment while NPCs (>=1002) do', () => {
  assert.equal(shouldEnrichBeatWithCeleris(1000), false);
  assert.equal(shouldEnrichBeatWithCeleris(1001), false);
  assert.equal(shouldEnrichBeatWithCeleris(1002), true);
  assert.equal(shouldEnrichBeatWithCeleris(1012), true);
});

test('IncrementalOpusTupleScanner emits each completed tuple in real time across arbitrary chunk splits', () => {
  const scanner = new IncrementalOpusTupleScanner();
  const fullPayload =
    '[D]: [[1002, "😱", "Wait [what]?! \\"No way!\\""], [1003, "🤔", "Step aside.", "They suspect nothing."]]';

  const streamedTuples: RawDialogueTuple[] = [];
  for (let i = 0; i < fullPayload.length; i += 3) {
    const chunk = fullPayload.slice(i, i + 3);
    const newlyCompleted = scanner.appendChunk(chunk);
    for (const tuple of newlyCompleted) {
      streamedTuples.push(tuple);
      if (streamedTuples.length === 1) {
        assert.equal(scanner.dArrayClosed, false);
        assert.deepEqual(tuple, [1002, '😱', 'Wait [what]?! "No way!"']);
      }
    }
  }

  assert.equal(scanner.dArrayClosed, true);
  assert.equal(streamedTuples.length, 2);
  assert.deepEqual(streamedTuples[1], [1003, '🤔', 'Step aside.', 'They suspect nothing.']);
});

test('IncrementalOpusTupleScanner handles <think> block, markdown fences, bare [[, and empty [D]: []', () => {
  const thinkScanner = new IncrementalOpusTupleScanner();
  assert.deepEqual(thinkScanner.appendChunk('<think>planning beats'), []);
  assert.deepEqual(thinkScanner.appendChunk('</think>\n```json\n[D]: [[1002, "😏", "Nice try."]]\n```'), [
    [1002, '😏', 'Nice try.']
  ]);
  assert.equal(thinkScanner.dArrayClosed, true);

  const bareScanner = new IncrementalOpusTupleScanner();
  assert.deepEqual(bareScanner.appendChunk('  [[1002, "🙂", "Hello"]]'), [[1002, '🙂', 'Hello']]);
  assert.equal(bareScanner.dArrayClosed, true);

  const emptyScanner = new IncrementalOpusTupleScanner();
  assert.deepEqual(emptyScanner.appendChunk('[D]: []'), []);
  assert.equal(emptyScanner.dArrayClosed, true);
});

test('Mid-stream authorization allows clean short [1000, ...] Opus beats while rejecting 1001, forbidden tags, and unauthorized NPCs', () => {
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1000, 'A scroll slides off the desk and hits her ear.'], [1002]), true);
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1000, 'Narrator [TURN_JSON] leak'], [1002]), false);
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1001, 'Player echo'], [1002]), false);
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1005, '😈', 'Unauthorized!'], [1002]), false);
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1002, '😇', 'Follow me!'], [1002]), true);
  assert.equal(isValidAuthorizedMidStreamNpcTuple([1002, '😶', '', 'Secret thought'], [1002]), true);
});

test('clampShortOpusNarration keeps Opus [1000] beats to one crisp short sentence (<=16 words)', () => {
  const multi = 'A stack of Heaven forms slides off the edge and bonks her head cleanly. Meanwhile the gate hums loudly beside both of you.';
  const clamped = clampShortOpusNarration(multi, 16, 140);
  assert.equal(clamped, 'A stack of Heaven forms slides off the edge and bonks her head cleanly.');
  assert(clamped.split(/\s+/).length <= 16);

  const longSingle = 'Across the crowded marble plaza a trembling feathered pen rolls steadily under the heavy oak lectern toward your boots.';
  const clampedLong = clampShortOpusNarration(longSingle, 16, 140);
  assert(clampedLong.split(/\s+/).length <= 16);
  assert(clampedLong.length <= 140);
  assert.match(clampedLong, /[.!?…]$/);

  const withAbbr = 'The Lv.999 angel wobbles on her heels. She nearly trips.';
  assert.equal(clampShortOpusNarration(withAbbr, 16, 140), 'The Lv.999 angel wobbles on her heels.');
});

test('isNearDuplicateBeat0Narration suppresses Beat 0 echoes while keeping distinct short action beats', () => {
  const beat0 = 'Golden light shimmers across the marble chamber while parchment litters her messy desk.';
  assert.equal(isNearDuplicateBeat0Narration(beat0, beat0), true);
  assert.equal(
    isNearDuplicateBeat0Narration(beat0, 'Golden light shimmers across the marble chamber right now.'),
    true
  );
  assert.equal(
    isNearDuplicateBeat0Narration(beat0, 'A stray feather drops onto her nose.'),
    false
  );
});

test('extractCompleteJsonStringField streams GPT-OSS narrator as soon as its closing quote completes', () => {
  const chunk1 = '<think>checking physics</think>{"verdict":"3_STARS","reason":"Valid move.","narrator":"Marble dust swirls';
  assert.equal(extractCompleteJsonStringField(chunk1, 'verdict'), '3_STARS');
  assert.equal(extractCompleteJsonStringField(chunk1, 'narrator'), null);

  const chunk2 = chunk1 + ' beside the gate as \\"error\\" sparks hiss.", "turn_json":{"s":{"z":"Hall';
  assert.equal(
    extractCompleteJsonStringField(chunk2, 'narrator'),
    'Marble dust swirls beside the gate as "error" sparks hiss.'
  );
  assert.equal(extractCompleteJsonStringField('<think>still thinking', 'verdict'), null);
});

test('GPT-OSS Beat 0 immediate dispatch + short Opus [1000] + concurrent NPC beats reconcile without duplication', () => {
  const tracker = createTurnBeatDispatcherState();

  const beat0 = recordDispatchedBeat(tracker, 1000, 'Torchlight flickers across the marble gate while embers snap overhead.');
  assert.equal(beat0.beatIndex, 0);
  assert.equal(beat0.usedCelerisEnricher, false);

  const scanner = new IncrementalOpusTupleScanner();
  const chunk1 = scanner.appendChunk('[D]: [[1002, "😤", "Quit staring at the tome!"],');
  assert.equal(chunk1.length, 1);
  assert.equal(isValidAuthorizedMidStreamNpcTuple(chunk1[0], [1002]), true);
  const beat1 = recordDispatchedBeat(tracker, Number(chunk1[0][0]), String(chunk1[0][2]));
  assert.equal(beat1.beatIndex, 1);
  assert.equal(beat1.usedCelerisEnricher, true);

  const chunk2 = scanner.appendChunk(' [1000, "A scroll smacks her ear."],');
  assert.equal(chunk2.length, 1);
  assert.equal(isValidAuthorizedMidStreamNpcTuple(chunk2[0], [1002]), true);
  const beat2 = recordDispatchedBeat(tracker, 1000, String(chunk2[0][1]));
  assert.equal(beat2.beatIndex, 2);
  assert.equal(beat2.usedCelerisEnricher, false);

  const chunk3 = scanner.appendChunk(' [1002, "😶", "", "Hope he skips page four."]]');
  assert.equal(chunk3.length, 1);
  const beat3 = recordDispatchedBeat(tracker, Number(chunk3[0][0]), String(chunk3[0][3]));
  assert.equal(beat3.beatIndex, 3);
  assert.equal(beat3.sig, computeBeatContentSig(1002, 'Hope he skips page four.'));

  const finalTuples: RawDialogueTuple[] = [
    [1000, 'Torchlight flickers across the marble gate while embers snap overhead.'],
    [1002, '😤', 'Quit staring at the tome!'],
    [1000, 'A scroll smacks her ear.'],
    [1002, '😶', '', 'Hope he skips page four.']
  ];
  assert.deepEqual(findMissingPostStreamTuples(tracker, finalTuples), []);
});

test('Silent inline brace-only thought tuples match between mid-stream dispatch and final reconciliation', () => {
  const tracker = createTurnBeatDispatcherState();
  recordDispatchedBeat(tracker, 1000, 'Candles flicker along the corridor.');
  recordDispatchedBeat(tracker, 1002, 'They suspect nothing.');

  const finalTuples: RawDialogueTuple[] = [
    [1000, 'Candles flicker along the corridor.'],
    [1002, '😒', '{They suspect nothing.}']
  ];
  assert.deepEqual(findMissingPostStreamTuples(tracker, finalTuples), []);
});

test('extractOpusDialogueTuples recovers single-bracket, missing closing ], trailing commas, triple nesting, objects, and unescaped quotes', () => {
  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [1002, "😅", "Just a tiny clerical quirk!"]'),
    [[1002, '😅', 'Just a tiny clerical quirk!']]
  );

  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [1002, "😅", "One!"], [1000, "A scroll slips."]'),
    [[1002, '😅', 'One!'], [1000, 'A scroll slips.']]
  );

  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [[1002, "😱", "Wait!"], [1000, "She drops a scroll."],'),
    [[1002, '😱', 'Wait!'], [1000, 'She drops a scroll.']]
  );

  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [[[1002, "😅", "Wait!"]]]'),
    [[1002, '😅', 'Wait!']]
  );

  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [{"uid": 1002, "emoji": "😅", "text": "Step aside!"}]'),
    [[1002, '😅', 'Step aside!']]
  );

  assert.deepEqual(
    extractOpusDialogueTuples('[D]: [[1002, "😱", "Wait!"], [1002, "😏", "They call it "heroic" training."]]'),
    [[1002, '😱', 'Wait!'], [1002, '😏', 'They call it "heroic" training.']]
  );
});

