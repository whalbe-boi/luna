import { createRequire } from 'node:module';
import * as opusBeatStream from './src/lib/opusBeatStream.ts';

const require = createRequire(import.meta.url);
const engine = require('./server-engine.cjs') as {
  app: import('express').Express;
  PORT: number;
  initOpusBeatStream: (mod: typeof opusBeatStream) => void;
  finalizeEngineFallbacks: (extraMiddleware?: unknown) => void;
  describeCredentialState: () => { ready: boolean; source: string };
};

engine.initOpusBeatStream(opusBeatStream);

async function bootstrapServer() {
  const isProd = process.env.NODE_ENV === 'production';

  if (!isProd) {
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: 'custom',
    });
    engine.finalizeEngineFallbacks(vite.middlewares);
  } else {
    engine.finalizeEngineFallbacks();
  }

  const port = Number(process.env.PORT) || engine.PORT || 3000;
  const host = process.env.HOST || '0.0.0.0';

  const httpServer = engine.app.listen(port, host, () => {
    console.log(`Luna RPG engine listening on http://${host}:${port}`);
    const credState = engine.describeCredentialState();
    console.log(
      credState.ready
        ? `[Config] Credentials loaded from ${credState.source}.`
        : '[Config] Waiting for credentials via API Keys dialog or .env.'
    );
  });

  httpServer.on('error', (err: NodeJS.ErrnoException) => {
    if (err && err.code === 'EADDRINUSE') {
      console.error(`Port ${port} is already in use.`);
    } else {
      console.error('[Server Error]', err?.message || err);
    }
    process.exit(1);
  });
}

bootstrapServer().catch((err) => {
  console.error('[Bootstrap Error]', err);
  process.exit(1);
});
