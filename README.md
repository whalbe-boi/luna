<div align="center">
<img width="1200" height="475" alt="GHBanner" src="https://ai.google.dev/static/site-assets/images/share-ais-513315318.png" />
</div>

# Luna 3D RPG Visual Novel Studio

Real-time AI-directed 3D RPG Visual Novel engine with concurrent Claude Haiku (emtf) beat streaming, instant Beat 0 narrator speech synthesis, Cerebras GPT-OSS reasoning + authoritative `[TURN_JSON]`, Celeris micro-enrichment, and a tactical radar.

View your app in AI Studio: https://ai.studio/apps/75fc8f54-97e0-49ed-bcc1-0ecd1ea20065

## Features

- **Concurrent Haiku beat streaming** — Claude Haiku 5.5 (emtf) writes and streams the `[D]:` dialogue beats in real time; every `[TURN_JSON]` end state is authored by Cerebras GPT-OSS.
- **Instant Beat 0 narrator speech** — the opening narrator line is synthesized immediately.
- **Cerebras GPT-OSS reasoning** — high-effort reasoning pre-pass via Cerebras GPT-OSS 120B, including the authoritative end-of-turn `[TURN_JSON]`.
- **Celeris micro-enrichment** — secondary enrichment pass for dialogue and scene detail.
- **Tactical radar** — live tactical state derived from the authored turn.
- **Server-authored opening turn** — the opening turn is generated server-side for consistency.

## Tech Stack

- **Frontend:** React 19, TypeScript, Vite, Tailwind CSS v4, Motion
- **Backend:** Node.js, Express, tsx
- **AI providers:** Google Gemini (GenAI), emtf (Claude Haiku 5.5, dialogue only), Cerebras (GPT-OSS, reasoning + `[TURN_JSON]`), Celeris/Mercury, Leonardo (image generation), Cartesia (speech), Epidemic Sound (audio)
- **Tooling:** TypeScript, ESLint (tsc `--noEmit`)

## Project Structure

```
.
├── index.html              # Vite entry (root stub)
├── public/                 # Static assets & served index.html
├── src/
│   ├── main.tsx            # React entry point
│   ├── App.tsx             # Root component
│   ├── index.css           # Global styles
│   └── lib/
│       ├── opusBeatStream.ts        # Beat tuple scanner
│       └── *.test.ts               # Streaming integration tests
├── server.ts               # Express/Vite bootstrap
├── server-engine.cjs       # Core engine (AI orchestration, routes)
├── vite.config.ts
├── tsconfig.json
└── package.json
```

## Run Locally

**Prerequisites:** Node.js (see `package.json` engines where applicable).

1. Install dependencies:
   ```bash
   npm install
   ```
2. Configure environment variables (see below). At minimum set `GEMINI_API_KEY`.
3. Run the app:
   ```bash
   npm run dev
   ```
   The engine listens on `http://0.0.0.0:3000` by default.

## Environment Variables

Copy `.env.example` to `.env` (or `.env.local`) and fill in the values. The engine reads these from the process environment (and optionally from a file pointed to by `LUNA_ENV_FILE`).

| Variable | Description | Default |
| --- | --- | --- |
| `GEMINI_API_KEY` | Google Gemini API key (required) | — |
| `APP_URL` | Public URL of the hosted app | — |
| `PORT` | Server port | `3000` |
| `HOST` | Bind host | `0.0.0.0` |
| `EMTF_API_URL` (legacy: `PATEWAY_API_URL` / `THREEROUTER_API_URL`) | Haiku dialogue endpoint (Anthropic `/v1/messages`, streamed with `thinking: disabled`) | `https://emtf.aipm9527.online/v1/messages` |
| `EMTF_API_KEY` (legacy: `PATEWAY_API_KEY` / `THREEROUTER_API_KEY`) | Haiku API key (`sk-...`) | built-in default |
| `EMTF_MODEL` (legacy: `PATEWAY_MODEL` / `THREEROUTER_MODEL`) | Haiku dialogue model | `claude-haiku-5-5` |
| `CEREBRAS_API_URL` | Cerebras endpoint | `https://api.cerebras.ai/v1/chat/completions` |
| `CEREBRAS_API_KEY` | Cerebras API key | built-in default |
| `CEREBRAS_MODEL` | Cerebras model (also authors the authoritative `[TURN_JSON]`) | `gpt-oss-120b` |
| `CELERIS_API_URL` / `MERCURY_API_URL` / `LUNA_API_URL` | Celeris/Mercury endpoint | `https://inference.celeris.ai/...` |
| `CELERIS_API_KEY` / `MERCURY_API_KEY` / `LUNA_API_KEY` | Celeris API key | — |
| `LEONARDO_API_KEY` / `LEONARDO_TOKEN` | Leonardo image-generation key | — |
| `CARTESIA_API_KEY` | Cartesia speech-synthesis key | — |
| `EPIDEMIC_SOUND_API_KEY` / `ES_API_KEY` | Epidemic Sound audio key | built-in default |
| `DISABLE_HMR` | Disable Vite HMR (`true`/`false`) | — |
| `LUNA_ENV_FILE` | Path to an alternate env file | — |
| `NODE_ENV` | `production` enables production mode | — |

> Note: several provider keys ship with built-in defaults for development. Override them via environment variables for your own deployment. Never commit real secrets.

## Scripts

| Command | Description |
| --- | --- |
| `npm run dev` | Start the dev server with Vite middleware (`tsx server.ts`) |
| `npm run start` | Run the server directly (`node server.ts`) |
| `npm run build` | Build the frontend with Vite |
| `npm run preview` | Preview the production build |
| `npm run clean` | Remove `dist` and `server.js` |
| `npm run lint` | Type-check with `tsc --noEmit` |

## Notes

- In development the server boots Vite in middleware mode for HMR; in production (`NODE_ENV=production`) it serves the built assets.
- Test artifacts (`opus.txt`, `campaign_snapshots/.../campaign_default.json`) are generated by the test suite and are restored by `.gitignore`-adjacent test cleanup; do not commit them.
- The client consumes the authored `[TURN_JSON]` marker produced by Cerebras; see `src/lib/opusBeatStream.ts`. Haiku writes dialogue only and never emits state objects.

## License

See the `@license` header in source files (Apache-2.0 for `src/App.tsx`).