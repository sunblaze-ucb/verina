# preview/ React migration — design

**Date:** 2026-04-19
**Scope:** Re-platform `preview/` from vanilla Vite + Tailwind + JS to React 19 + TypeScript + Tailwind v4. Visual output preserved exactly; content unchanged; URLs unchanged.

## Context

Current `preview/`:
- `index.html` (625 lines) — 13 sections plus nav/footer
- `src/main.js` (43 lines) — hljs init, sticky-nav scroll listener, scroll-reveal IntersectionObserver, `copyBibtex`
- `src/style.css` (455 lines) — custom palette on top of Tailwind v4
- `public/images/` (11 PNGs)
- `vite.config.js` with `base: CF_PAGES ? '/' : '/preview/'`

Reference for conventions: sibling `verisyn-website/` (React 19 + Vite 8 + TS + Tailwind v4).

## Decisions

| | Chosen | Alternative rejected |
|---|---|---|
| Directory | Replace `preview/` in place | Side-by-side; redundant given git history |
| Language | TypeScript | JS; TS matches `verisyn-website` conventions |
| Granularity | One component per section + small shared helpers (`SectionLabel`, `CodeBlock`) | Single `App.tsx`; data-driven extraction (premature) |
| Styling | Port `style.css` verbatim | shadcn tokens; would be a redesign, not a re-platform |
| Highlighting | `highlight.js` + `highlightjs-lean` npm | CDN `<script>`; shiki (overkill for ~5 blocks) |
| Router | None (anchor links) | `react-router` (unnecessary) |
| Cloudflare | Keep `CF_PAGES` env branch in vite config | `@cloudflare/vite-plugin` + `wrangler` (not needed unless SSR) |

## Toolchain

Runtime deps: `react@^19`, `react-dom@^19`, `highlight.js`, `highlightjs-lean`, `clsx`, `tailwind-merge`.

Dev deps: `@vitejs/plugin-react`, `@types/react`, `@types/react-dom`, `typescript`, `vite@^8`, `tailwindcss@^4`, `@tailwindcss/vite`.

Config files: `tsconfig.json` with references to `tsconfig.app.json` + `tsconfig.node.json` (strict, `jsx: react-jsx`, `paths: { "@/*": ["./src/*"] }`). `vite.config.ts` ports current config and adds `react()` + `@` alias.

Scripts: `dev: vite`, `build: tsc -b && vite build`, `preview: vite preview`.

## File layout

```
preview/
  index.html                   shell only: <head> + <div id="root"> + script
  package.json
  tsconfig.json / .app / .node
  vite.config.ts
  public/images/...            unchanged
  src/
    main.tsx
    App.tsx                    composes sections
    index.css                  port of style.css + @import "tailwindcss"
    vite-env.d.ts
    lib/
      utils.ts                 cn() helper
      bibtex.ts                BibTeX string constant
    hooks/
      useStickyNav.ts
      useScrollReveal.ts
    components/
      Nav.tsx
      Hero.tsx
      InfoStrip.tsx
      Abstract.tsx
      Overview.tsx
      Features.tsx
      DataFormat.tsx
      SpecEval.tsx
      Statistics.tsx
      Results.tsx
      Combinations.tsx
      GetStarted.tsx
      Citation.tsx
      Acknowledgements.tsx
      Footer.tsx
      SectionLabel.tsx
      CodeBlock.tsx
```

## State & data flow

- No global state. Content is static JSX in each section.
- `useStickyNav` — `scroll` listener → boolean; consumed by `<Nav>` for `.scrolled` class.
- `useScrollReveal` — one `IntersectionObserver` at `App` level; components opt in via `<div data-reveal>`.
- `CodeBlock` — registers `lean` with hljs once at module load; calls `hljs.highlightElement(ref.current)` on mount; guards against re-highlight via `data-highlighted`.
- `Citation` — local `useState` for Copy/Copied label toggle.

## Styling

`index.css` = current `style.css` verbatim + `@import "tailwindcss"`. Custom rules (`.hero-gradient`, `.section-alt`, `.nav.scrolled`, `.data-table`, `.reveal`, `.section-label`) preserved unchanged.

Google Fonts stay as `<link>` tags in `index.html`. `highlight.js/styles/atom-one-dark.css` imported in `main.tsx` (drops the CDN `<link>`).

## Edge cases

- Scroll listener + IntersectionObserver cleanup in `useEffect` return.
- Clipboard API wrapped in try/catch with `document.execCommand('copy')` fallback.
- `hljs.highlightElement` guarded against double-highlight.

## Verification

Visual parity is the test.
1. `pnpm install && pnpm run build` succeeds; `tsc -b` passes with zero errors.
2. `pnpm run dev` → `http://localhost:5173/preview/`; eyeball each section against the currently deployed site.
3. Smoke checks: nav turns opaque on scroll; sections fade in; Lean code blocks highlight; BibTeX copy button flips to "Copied!".

No unit tests — static marketing page, no business logic.

## Deployment

Unchanged. `vite build` → `dist/`. Cloudflare Pages uses `CF_PAGES` env var to flip `base` from `/preview/` to `/`.
