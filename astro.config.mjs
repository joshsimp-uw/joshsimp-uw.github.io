// @ts-check
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'astro/config';

/**
 * URLs printed on physical material (the Networking Tetris poster and its QR code
 * in the networking lab). They must keep resolving at these exact paths.
 */
const PERMANENT_URLS = ['network-tetris.html', 'network-tetris.css', 'network-tetris.js'];

/** @returns {import('astro').AstroIntegration} */
function permanentUrls() {
  return {
    name: 'permanent-urls',
    hooks: {
      'astro:build:done': ({ dir }) => {
        const missing = PERMANENT_URLS.filter((p) => !existsSync(fileURLToPath(new URL(p, dir))));
        if (missing.length > 0) {
          throw new Error(`Permanent URLs missing from build output: ${missing.join(', ')}`);
        }
      },
    },
  };
}

// https://astro.build/config
export default defineConfig({
  site: 'https://joshsimp-uw.github.io',
  integrations: [permanentUrls()],
});
