import test from 'node:test';
import assert from 'node:assert/strict';
import http from 'node:http';
import { once } from 'node:events';
import { createRequire } from 'node:module';
import path from 'node:path';
import * as opusBeatStream from './opusBeatStream.ts';

const require = createRequire(import.meta.url);

interface RecordedSseEvent {
  atMs: number;
  raw: string;
  json: Record<string, any> | null;
}

test('E2E /api/chat/stream suite', async (t) => {
  let activeMockHandler: (req: http.IncomingMessage, res: http.ServerResponse, parsedBody: any) => void =
    (_req, res) => { res.writeHead(404); res.end('Not found'); };

  const mockUpstream = http.createServer(async (req, res) => {
    const chunks: Buffer[] = [];
    for await (const c of req) chunks.push(c as Buffer);
    const bodyStr = Buffer.concat(chunks).toString('utf8');
    let parsedBody: any = {};
    try {
      parsedBody = JSON.parse(bodyStr || '{}');
    } catch {}
    activeMockHandler(req, res, parsedBody);
  });

  mockUpstream.listen(0, '127.0.0.1');
  await once(mockUpstream, 'listening');
  const upstreamAddr = mockUpstream.address();
  assert(upstreamAddr && typeof upstreamAddr === 'object');
  const baseUrl = `http://127.0.0.1:${upstreamAddr.port}`;

  process.env.CEREBRAS_API_URL = `${baseUrl}/cerebras`;
  process.env.CELERIS_API_URL = `${baseUrl}/celeris`;
  process.env.MERCURY_API_URL = `${baseUrl}/celeris`;
  process.env.INCEPTION_MERCURY_API_URL = `${baseUrl}/celeris`;
  process.env.PATEWAY_API_URL = `${baseUrl}/opus`;
  process.env.THREEROUTER_API_URL = `${baseUrl}/opus`;
  process.env.CEREBRAS_API_KEY = 'test-cerebras-key';
  process.env.CELERIS_API_KEY = 'ck_test_celeris_key';
  process.env.MERCURY_API_KEY = 'ck_test_celeris_key';
  process.env.PATEWAY_API_KEY = 'test-opus-key';
  process.env.THREEROUTER_API_KEY = 'test-opus-key';
  process.env.CARTESIA_API_KEY = '';
  process.env.LEONARDO_API_KEY = '';

  const engine = require(path.resolve(process.cwd(), 'server-engine.cjs'));
  engine.initOpusBeatStream(opusBeatStream);
  engine.finalizeEngineFallbacks(null);

  const appServer = engine.app.listen(0, '127.0.0.1');
  await once(appServer, 'listening');
  const appAddr = appServer.address();
  assert(appAddr && typeof appAddr === 'object');
  const appUrl = `http://127.0.0.1:${appAddr.port}`;

  try {
    await t.test('streams GPT-OSS standard Beat 0 before turn_json completes, routes NPC micro-enricher to Celeris (celeris-1, never Beat 0/UID 1000), clamps short Opus [1000] beats, and suppresses Beat 0 echoes', async () => {
      const celerisEnrichRequests: Array<{ beat_index: number; uid: number; text: string; model: string }> = [];
      const unexpectedRoutes: string[] = [];
      let cerebrasTurnJsonSentAt = 0;
      let opusChunk1SentAt = 0;
      let opusChunk2SentAt = 0;
      let opusChunk4SentAt = 0;

      const standardBeat0Narrator =
        'Golden light shimmers across the marble floor while loose parchment flutters off the Catgirl Angel\'s messy desk. Dust motes dance around the blinking red error pedestal beside your boots.';

      activeMockHandler = (req, res, parsedBody) => {
        if (req.url === '/celeris') {
          const modelStr = String(parsedBody?.model || '');
          assert.equal(modelStr, 'celeris-1', 'Celeris route must use standard celeris-1, never celeris-1-magnus');
          assert.equal(/magnus|magnum/i.test(modelStr), false);

          const userText = String(parsedBody?.messages?.[1]?.content || '');
          if (userText.includes('"mode"')) {
            try {
              const promptObj = JSON.parse(userText);
              celerisEnrichRequests.push({
                beat_index: Number(promptObj.beat_index),
                uid: Number(promptObj.uid),
                text: String(promptObj.text || ''),
                model: modelStr
              });
            } catch {}

            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({
              choices: [{
                message: {
                  content: JSON.stringify({
                    qualifiers: 'nervously waving toward the swirling gate',
                    visual_impact: 'sweat_drop',
                    is_moving: true,
                    sticker_anim: 'bounce'
                  })
                }
              }]
            }));
            return;
          }

          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ choices: [{ message: { content: '{}' } }] }));
          return;
        }

        if (req.url === '/cerebras') {
          assert.equal(parsedBody?.stream, true, 'Stage-1 Cerebras must request SSE streaming for Beat 0 concurrency');
          res.writeHead(200, {
            'Content-Type': 'text/event-stream',
            'Cache-Control': 'no-cache',
            Connection: 'keep-alive'
          });

          const writeCerebrasDelta = (text: string) => {
            res.write(`data: ${JSON.stringify({
              choices: [{ delta: { content: text } }]
            })}\n\n`);
          };

          const headPart = JSON.stringify({
            verdict: '3_STARS',
            reason: 'Valid present-tense action.',
            active_action: 'Observing the chamber',
            bgm_hint: 'KEEP',
            causal_outcome: 'A stray scroll tumbles off her desk.',
            speaker_uids: [1002],
            narrator: standardBeat0Narrator
          }).slice(0, -1);

          writeCerebrasDelta(headPart + ',');

          setTimeout(() => {
            cerebrasTurnJsonSentAt = Date.now();
            const tailPart = JSON.stringify({
              turn_json: {
                s: {
                  z: 'Heavenly Reincarnation Chamber',
                  spot: 'Before the Reincarnation Gate'
                },
                d: { t: 5 }
              }
            }).slice(1);
            writeCerebrasDelta(tailPart);
            res.write('data: [DONE]\n\n');
            res.end();
          }, 220);
          return;
        }

        if (req.url === '/opus') {
          res.writeHead(200, {
            'Content-Type': 'text/event-stream',
            'Cache-Control': 'no-cache',
            Connection: 'keep-alive'
          });

          const writeAnthropicDelta = (text: string) => {
            res.write(`data: ${JSON.stringify({
              type: 'content_block_delta',
              index: 0,
              delta: { type: 'text_delta', text }
            })}\n\n`);
          };

          opusChunk1SentAt = Date.now();
          writeAnthropicDelta('[D]: [[1002, "😱", "Wait—don\'t read that blinking red error!"]');

          setTimeout(() => {
            opusChunk2SentAt = Date.now();
            writeAnthropicDelta(', [1000, "A wobbling stack of Heaven forms slides off her desk and smacks her ear. Dust settles over both sandals."]');

            setTimeout(() => {
              writeAnthropicDelta(`, [1000, ${JSON.stringify(standardBeat0Narrator)}]`);
              opusChunk4SentAt = Date.now();
              writeAnthropicDelta(', [1002, "😅", "Look over at this shiny portal instead!"]]');
              res.write(`data: ${JSON.stringify({ type: 'message_stop' })}\n\n`);
              res.end();
            }, 140);
          }, 160);
          return;
        }

        unexpectedRoutes.push(String(req.url || ''));
        res.writeHead(404);
        res.end('Not found');
      };

      const healthRes = await fetch(`${appUrl}/api/health`, {
        headers: { 'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN }
      });
      assert.equal(healthRes.status, 200);
      const healthJson: any = await healthRes.json();
      assert.equal(healthJson.decorator_model, 'celeris-1');
      assert.equal(healthJson.providers_configured?.celeris, true, 'Health must report celeris provider configured');
      assert.equal(healthJson.providers_configured?.cerebras, true, 'Health must report cerebras provider configured');

      const startMs = Date.now();
      const response = await fetch(`${appUrl}/api/chat/stream`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN
        },
        body: JSON.stringify({
          playerActionText: 'Look around the room',
          playerDialogueText: 'Wait a minute!',
          dialoguePayload: {
            messages: [{ role: 'user', content: 'Look around the room' }]
          }
        })
      });

      assert.equal(response.status, 200);
      assert(response.body, 'SSE response body should exist');

      const events: RecordedSseEvent[] = [];
      const reader = response.body.getReader();
      const decoder = new TextDecoder();
      let sseBuf = '';

      while (true) {
        const { value, done } = await reader.read();
        if (done) break;
        sseBuf += decoder.decode(value, { stream: true });
        let sepIdx: number;
        while ((sepIdx = sseBuf.indexOf('\n\n')) !== -1) {
          const frame = sseBuf.slice(0, sepIdx);
          sseBuf = sseBuf.slice(sepIdx + 2);
          for (const line of frame.split('\n')) {
            if (!line.startsWith('data: ')) continue;
            const payload = line.slice(6).trim();
            if (!payload) continue;
            let parsed: Record<string, any> | null = null;
            if (payload !== '[DONE]') {
              try { parsed = JSON.parse(payload); } catch {}
            }
            events.push({ atMs: Date.now() - startMs, raw: payload, json: parsed });
          }
        }
      }

      const extracted = events.filter(e => e.json?.beat_extracted);
      assert.equal(extracted.length, 4, `Expected 4 unique beat_extracted events, got ${extracted.length}`);

      const beat0Event = extracted[0];
      const beat1Event = extracted[1];
      const beat2Event = extracted[2];
      const beat3Event = extracted[3];

      assert.equal(beat0Event.json!.beat_extracted.beat_index, 0);
      assert.equal(beat0Event.json!.beat_extracted.uid, 1000);
      assert.equal(beat0Event.json!.beat_extracted.emotion, 'neutral');
      assert(
        String(beat0Event.json!.beat_extracted.dialogue || '').split(/\s+/).length >= 20,
        'GPT-OSS Beat 0 should retain full standard narration length'
      );
      const prepassDoneEvent = events.find(e => e.json?.prepass_status === 'done');
      assert(prepassDoneEvent, 'Expected prepass_status: done');
      assert(events.indexOf(beat0Event) < events.indexOf(prepassDoneEvent), 'Beat 0 must emit mid-Stage-1 before prepass_status: done');
      assert(
        beat0Event.atMs < (cerebrasTurnJsonSentAt - startMs),
        `Beat 0 (${beat0Event.atMs}ms) must stream BEFORE Stage-1 turn_json completes (${cerebrasTurnJsonSentAt - startMs}ms)`
      );

      const opusDoneEvent = events.find(e => e.json?.opus_done === true);
      assert(opusDoneEvent, 'Expected opus_done event');
      assert.equal(beat1Event.json!.beat_extracted.beat_index, 1);
      assert.equal(beat1Event.json!.beat_extracted.uid, 1002);
      assert(
        beat1Event.atMs < (opusChunk2SentAt - startMs),
        `Beat 1 (${beat1Event.atMs}ms) should dispatch concurrently before Opus Chunk 2 (${opusChunk2SentAt - startMs}ms)`
      );

      assert.equal(beat2Event.json!.beat_extracted.beat_index, 2);
      assert.equal(beat2Event.json!.beat_extracted.uid, 1000);
      assert.equal(beat2Event.json!.beat_extracted.emotion, 'neutral');
      const shortOpusNarr = String(beat2Event.json!.beat_extracted.dialogue || '');
      assert.equal(
        shortOpusNarr,
        'A wobbling stack of Heaven forms slides off her desk and smacks her ear.'
      );
      assert(shortOpusNarr.split(/\s+/).length <= 16, 'Opus [1000] narration must stay <= 16 words');
      assert(
        beat2Event.atMs < (opusChunk4SentAt - startMs),
        `Beat 2 (${beat2Event.atMs}ms) should dispatch concurrently before Opus Chunk 4 (${opusChunk4SentAt - startMs}ms)`
      );

      assert.equal(beat3Event.json!.beat_extracted.beat_index, 3);
      assert.equal(beat3Event.json!.beat_extracted.uid, 1002);

      assert.equal(
        celerisEnrichRequests.some(r => r.uid === 1000 || r.beat_index === 0 || r.beat_index === 2),
        false,
        'Narrator UID 1000 (both Beat 0 and short Opus beats) must NEVER call Celeris micro-enrichment'
      );
      assert(celerisEnrichRequests.some(r => r.uid === 1002 && r.beat_index === 1 && r.model === 'celeris-1'));
      assert(celerisEnrichRequests.some(r => r.uid === 1002 && r.beat_index === 3 && r.model === 'celeris-1'));
      const enrichEvents = events.filter(e => e.json?.beat_enrich);
      assert.equal(enrichEvents.length, 2, 'Only NPC beats 1 and 3 should emit beat_enrich');

      assert.equal(unexpectedRoutes.length, 0, `Unexpected upstream calls: ${unexpectedRoutes.join(', ')}`);
      assert.ok(opusChunk1SentAt > 0 && opusChunk2SentAt > opusChunk1SentAt);
      assert.equal(events[events.length - 1]?.raw, '[DONE]');
    });

    await t.test('recovers cleanly when Opus omits outer closing ] or leaves a trailing comma after Beat 1', async () => {
      activeMockHandler = (req, res, _parsedBody) => {
        if (req.url === '/celeris') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{ message: { content: JSON.stringify({ qualifiers: 'sweating furiously', visual_impact: 'sweat_drop', is_moving: false, sticker_anim: 'bounce' }) } }]
          }));
          return;
        }
        if (req.url === '/cerebras') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{
              message: {
                content: JSON.stringify({
                  verdict: '3_STARS',
                  reason: 'Valid action.',
                  active_action: 'Checking the error pedestal',
                  bgm_hint: 'KEEP',
                  causal_outcome: 'A stray feather drifts across the desk.',
                  speaker_uids: [1002],
                  narrator: 'Golden light flickers across the marble floor while loose scrolls tilt toward the edge of the desk.',
                  turn_json: { s: { z: 'Heavenly Reincarnation Chamber', spot: 'Before the Reincarnation Gate' }, d: { t: 1 } }
                })
              }
            }]
          }));
          return;
        }

        if (req.url === '/opus') {
          res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache', Connection: 'keep-alive' });
          res.write(`data: ${JSON.stringify({
            type: 'content_block_delta',
            index: 0,
            delta: { type: 'text_delta', text: '[D]: [[1002, "😅", "HOLD ON! Look at the shiny portal instead!"], [1000, "A scroll slides off the desk."],' }
          })}\n\n`);
          res.write(`data: ${JSON.stringify({ type: 'message_stop' })}\n\n`);
          res.end();
          return;
        }

        res.writeHead(404);
        res.end('Not found');
      };

      const response = await fetch(`${appUrl}/api/chat/stream`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN
        },
        body: JSON.stringify({
          playerActionText: 'Inspect pedestal',
          playerDialogueText: '',
          dialoguePayload: { messages: [{ role: 'user', content: 'Inspect pedestal' }] }
        })
      });

      assert.equal(response.status, 200);
      assert(response.body);
      const bodyText = await response.text();
      assert.equal(bodyText.includes('stream_error'), false, `Stream must not error: ${bodyText}`);
      assert.equal(bodyText.includes('malformed dialogue tuple'), false);
      assert(bodyText.includes('"opus_done":true'));
      assert(bodyText.includes('HOLD ON! Look at the shiny portal instead!'));
      assert(bodyText.includes('A scroll slides off the desk.'));
      assert(bodyText.trimEnd().endsWith('data: [DONE]'));
    });

    await t.test('reconciles redundant d.l in same zone and omitted d.l on zone transition without stage/location mismatch', async () => {
      // Turn A: Same zone with redundant d.l, empty optional strings, and mw: 0
      activeMockHandler = (req, res, _parsedBody) => {
        if (req.url === '/celeris') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{ message: { content: JSON.stringify({ qualifiers: 'nodding', visual_impact: 'none', is_moving: false, sticker_anim: 'pop' }) } }]
          }));
          return;
        }
        if (req.url === '/cerebras') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{
              message: {
                content: JSON.stringify({
                  verdict: '3_STARS',
                  reason: 'Valid action.',
                  active_action: 'Stepping beside the pedestal',
                  bgm_hint: 'KEEP',
                  causal_outcome: 'You step right.',
                  speaker_uids: [1002],
                  narrator: 'Sparks pop across the marble pedestal while stacked scrolls wobble on the desk.',
                  turn_json: {
                    s: { z: 'Heavenly Reincarnation Chamber', spot: 'Right beside the pedestal' },
                    d: { t: 1, l: 'Heavenly Reincarnation Chamber', wth: '', o: '', mw: 0 }
                  }
                })
              }
            }]
          }));
          return;
        }
        if (req.url === '/opus') {
          res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache', Connection: 'keep-alive' });
          res.write(`data: ${JSON.stringify({ type: 'content_block_delta', index: 0, delta: { type: 'text_delta', text: '[D]: [[1002, "😅", "Watch your step!"]]' } })}\n\n`);
          res.write(`data: ${JSON.stringify({ type: 'message_stop' })}\n\n`);
          res.end();
          return;
        }
        res.writeHead(404);
        res.end('Not found');
      };

      const resSame = await fetch(`${appUrl}/api/chat/stream`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN },
        body: JSON.stringify({ playerActionText: 'Step right', dialoguePayload: { messages: [{ role: 'user', content: 'Step right' }] } })
      });
      assert.equal(resSame.status, 200);
      const txtSame = await resSame.text();
      assert.equal(txtSame.includes('stage/location mismatch'), false, txtSame);
      assert(txtSame.includes('"turn_resolution"'), txtSame);

      // Turn B: Zone change where GPT-OSS changes s.z + d.mw=1 and omits d.l
      activeMockHandler = (req, res, _parsedBody) => {
        if (req.url === '/celeris') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{ message: { content: JSON.stringify({ qualifiers: 'blinking in sunlight', visual_impact: 'sweat_drop', is_moving: true, sticker_anim: 'bounce' }) } }]
          }));
          return;
        }
        if (req.url === '/cerebras') {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{
              message: {
                content: JSON.stringify({
                  verdict: '3_STARS',
                  reason: 'Stepped through the gate.',
                  active_action: 'Standing at the outpost',
                  bgm_hint: 'KEEP',
                  causal_outcome: 'Both drop into Oakhaven.',
                  speaker_uids: [1002],
                  narrator: 'Light swallows the chamber and drops you onto muddy cobblestones outside a weathered frontier outpost.',
                  turn_json: {
                    s: { z: 'Oakhaven Border Outpost', spot: 'Muddy Gatehouse Cobblestones' },
                    d: { t: 2, mw: 1 }
                  }
                })
              }
            }]
          }));
          return;
        }
        if (req.url === '/opus') {
          res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache', Connection: 'keep-alive' });
          res.write(`data: ${JSON.stringify({ type: 'content_block_delta', index: 0, delta: { type: 'text_delta', text: '[D]: [[1002, "😱", "MY WINGS ARE GONE?!"]]' } })}\n\n`);
          res.write(`data: ${JSON.stringify({ type: 'message_stop' })}\n\n`);
          res.end();
          return;
        }
        res.writeHead(404);
        res.end('Not found');
      };

      const resMove = await fetch(`${appUrl}/api/chat/stream`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN },
        body: JSON.stringify({ playerActionText: 'Step through gate', dialoguePayload: { messages: [{ role: 'user', content: 'Step through gate' }] } })
      });
      assert.equal(resMove.status, 200);
      const txtMove = await resMove.text();
      assert.equal(txtMove.includes('stage/location mismatch'), false, txtMove);
      assert(txtMove.includes('"l":"Oakhaven Border Outpost"'), txtMove);
      assert(txtMove.trimEnd().endsWith('data: [DONE]'));
    });

    await t.test('routes /api/rpg/active-action and /api/rpg/instrumental through standard celeris-1 (no magnus)', async () => {
      const seenModels: string[] = [];
      let hitCelerisRoute = false;

      activeMockHandler = (req, res, parsedBody) => {
        if (req.url === '/celeris') {
          hitCelerisRoute = true;
          seenModels.push(String(parsedBody?.model || ''));
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({
            choices: [{
              message: {
                content: JSON.stringify({
                  player_action_status: 'Holding Silver Coin in R-HAND while standing beside the pedestal'
                })
              }
            }]
          }));
          return;
        }
        res.writeHead(404);
        res.end('Not found');
      };

      const resAction = await fetch(`${appUrl}/api/rpg/active-action`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'X-Luna-Session-Token': engine.SERVER_SESSION_TOKEN
        },
        body: JSON.stringify({
          currentStatus: 'Standing before the Reincarnation Gate',
          actionDescription: 'Holding 10 SP openly in RIGHT HAND',
          location: 'Heavenly Reincarnation Chamber'
        })
      });

      assert.equal(resAction.status, 200);
      const jsonAction: any = await resAction.json();
      assert.equal(hitCelerisRoute, true);
      assert.equal(jsonAction.source, 'celeris');
      assert.deepEqual(seenModels, ['celeris-1']);
      assert.equal(seenModels.some(m => /magnus|magnum/i.test(m)), false);
      assert(String(jsonAction.player_action_status || '').includes('Silver Coin'));
    });
  } finally {
    appServer.closeAllConnections?.();
    mockUpstream.closeAllConnections?.();
    appServer.close();
    mockUpstream.close();
  }
});

