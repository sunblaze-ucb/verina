# preview/ React Migration Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Re-platform `preview/` from vanilla Vite + Tailwind + JS to React 19 + TypeScript + Tailwind v4, preserving visual output exactly.

**Architecture:** One React component per HTML section (`Nav`, `Hero`, `InfoStrip`, `Abstract`, `Overview`, `Features`, `DataFormat`, `SpecEval`, `Statistics`, `Results`, `Combinations`, `GetStarted`, `Citation`, `Acknowledgements`, `Footer`), plus two shared helpers (`SectionLabel`, `CodeBlock`) and two custom hooks (`useStickyNav`, `useScrollReveal`). No data-driven extraction; content stays as JSX. CSS and images port verbatim.

**Tech Stack:** React 19, TypeScript ~6, Vite 8, Tailwind v4 (via `@tailwindcss/vite`), highlight.js (with highlightjs-lean), clsx, tailwind-merge. Conventions match sibling `verisyn-website/`.

**Reference files (read, do not skip):**
- `preview/index.html` (current, 625 lines) — source of truth for every section's markup
- `preview/src/style.css` (current, 455 lines) — ports verbatim to `preview/src/index.css`
- `preview/src/main.js` (current, 43 lines) — logic reimplemented as hooks
- Design doc: `docs/plans/2026-04-19-react-migration-design.md`

**Verification:** Static marketing page, no unit tests. The test is visual parity. Each task ends with either `tsc --noEmit` (after touching TS) or nothing (after docs/CSS only). Final verification: `pnpm run build` succeeds and `pnpm run dev` renders a page visually identical to the current deployed `preview/`.

**Commit policy:** Commit after each task. Messages follow the repo's style (no prefix convention; concise first line + blank + Co-Authored-By).

---

## Task 1: Replace toolchain scaffolding

**Files:**
- Delete: `preview/package.json`, `preview/pnpm-lock.yaml`, `preview/vite.config.js`, `preview/src/main.js`, `preview/src/style.css`, `preview/node_modules/` (let pnpm regenerate), `preview/dist/` (build artifact)
- Keep: `preview/index.html` (will be rewritten in Task 2), `preview/public/images/`
- Create: `preview/package.json`, `preview/vite.config.ts`, `preview/tsconfig.json`, `preview/tsconfig.app.json`, `preview/tsconfig.node.json`, `preview/src/vite-env.d.ts`

**Step 1: Remove generated artifacts**

```bash
rm -rf preview/node_modules preview/dist preview/pnpm-lock.yaml
```

**Step 2: Write `preview/package.json`**

```json
{
  "name": "preview",
  "version": "1.0.0",
  "private": true,
  "type": "module",
  "packageManager": "pnpm@10.32.1",
  "scripts": {
    "dev": "vite",
    "build": "tsc -b && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "clsx": "^2.1.1",
    "highlight.js": "^11.11.1",
    "highlightjs-lean": "^1.0.0",
    "react": "^19.2.5",
    "react-dom": "^19.2.5",
    "tailwind-merge": "^3.5.0"
  },
  "devDependencies": {
    "@tailwindcss/vite": "^4.2.1",
    "@types/react": "^19.2.14",
    "@types/react-dom": "^19.2.3",
    "@vitejs/plugin-react": "^6.0.1",
    "tailwindcss": "^4.2.1",
    "typescript": "~6.0.2",
    "vite": "^8.0.0"
  }
}
```

Note: if `highlightjs-lean@^1.0.0` does not resolve on npm, fall back to `"highlightjs-lean": "latest"` and pin after install.

**Step 3: Write `preview/vite.config.ts`**

```ts
import path from 'path'
import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'

export default defineConfig({
  base: process.env.CF_PAGES ? '/' : '/preview/',
  plugins: [react(), tailwindcss()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
})
```

**Step 4: Write `preview/tsconfig.json`**

```json
{
  "files": [],
  "references": [
    { "path": "./tsconfig.app.json" },
    { "path": "./tsconfig.node.json" }
  ]
}
```

**Step 5: Write `preview/tsconfig.app.json`**

```json
{
  "compilerOptions": {
    "tsBuildInfoFile": "./node_modules/.tmp/tsconfig.app.tsbuildinfo",
    "paths": { "@/*": ["./src/*"] },
    "target": "ES2020",
    "useDefineForClassFields": true,
    "lib": ["ES2020", "DOM", "DOM.Iterable"],
    "module": "ESNext",
    "skipLibCheck": true,
    "moduleResolution": "bundler",
    "allowImportingTsExtensions": true,
    "isolatedModules": true,
    "moduleDetection": "force",
    "noEmit": true,
    "jsx": "react-jsx",
    "strict": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true,
    "noFallthroughCasesInSwitch": true,
    "noUncheckedSideEffectImports": true
  },
  "include": ["src"]
}
```

**Step 6: Write `preview/tsconfig.node.json`**

```json
{
  "compilerOptions": {
    "tsBuildInfoFile": "./node_modules/.tmp/tsconfig.node.tsbuildinfo",
    "target": "ES2022",
    "lib": ["ES2023"],
    "module": "ESNext",
    "skipLibCheck": true,
    "moduleResolution": "bundler",
    "allowImportingTsExtensions": true,
    "isolatedModules": true,
    "moduleDetection": "force",
    "noEmit": true,
    "strict": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true,
    "noFallthroughCasesInSwitch": true,
    "noUncheckedSideEffectImports": true
  },
  "include": ["vite.config.ts"]
}
```

**Step 7: Write `preview/src/vite-env.d.ts`**

```ts
/// <reference types="vite/client" />
```

**Step 8: Delete old JS files**

```bash
rm preview/vite.config.js preview/src/main.js preview/src/style.css
```

**Step 9: Install dependencies**

```bash
cd preview && pnpm install
```

Expected: clean install, lockfile regenerated, no errors. If `highlightjs-lean` fails to resolve, pin to whatever pnpm reports as latest and retry.

**Step 10: Commit**

```bash
git add preview/package.json preview/pnpm-lock.yaml preview/vite.config.ts \
        preview/tsconfig.json preview/tsconfig.app.json preview/tsconfig.node.json \
        preview/src/vite-env.d.ts
git rm preview/vite.config.js preview/src/main.js preview/src/style.css
git commit -m "preview: scaffold React + TS toolchain"
```

---

## Task 2: Shell — `index.html` + `main.tsx` + `index.css`

**Files:**
- Rewrite: `preview/index.html`
- Create: `preview/src/main.tsx`, `preview/src/index.css`, `preview/src/App.tsx` (placeholder)

**Step 1: Rewrite `preview/index.html`** — strip body content, leave head + `<div id="root">` + bundled script reference.

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>VERINA: Benchmarking Verifiable Code Generation</title>

  <meta name="description" content="VERINA is a high-quality benchmark enabling comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions. Published at ICLR 2026." />
  <meta property="og:title" content="VERINA: Benchmarking Verifiable Code Generation" />
  <meta property="og:description" content="189 manually curated coding tasks in Lean for evaluating verifiable code generation. Published at ICLR 2026." />
  <meta property="og:url" content="https://verina.io/preview/" />
  <meta property="og:image" content="https://verina.io/preview/images/verina_cropped_05.png" />
  <meta property="og:image:width" content="1200" />
  <meta property="og:image:height" content="630" />
  <meta name="twitter:card" content="summary_large_image" />
  <meta name="twitter:title" content="VERINA: Benchmarking Verifiable Code Generation" />
  <meta name="twitter:description" content="189 manually curated coding tasks in Lean for evaluating verifiable code generation. Published at ICLR 2026." />
  <meta name="twitter:image" content="https://verina.io/preview/images/verina_cropped_05.png" />
  <meta name="keywords" content="Verifiable Code Generation, Benchmark, LLM, Lean, Formal Verification, ICLR 2026" />

  <!-- Fonts -->
  <link rel="preconnect" href="https://fonts.googleapis.com" />
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&family=Plus+Jakarta+Sans:wght@600;700;800&family=JetBrains+Mono:wght@400;500&display=swap" rel="stylesheet" />

  <!-- Academicons -->
  <link rel="stylesheet" href="https://cdn.jsdelivr.net/gh/jpswalsh/academicons@1/css/academicons.min.css" />
</head>
<body>
  <div id="root"></div>
  <script type="module" src="/src/main.tsx"></script>
</body>
</html>
```

Removed compared to old index.html: highlight.js CDN `<link>` and `<script>` (will come from npm), direct `<link>` to style.css, the 580 lines of body markup.

**Step 2: Port `preview/src/style.css` → `preview/src/index.css`**

Copy the current contents of `preview/src/style.css` verbatim (the file was already deleted in Task 1; use git show to retrieve it: `git show HEAD~1:preview/src/style.css > preview/src/index.css`, then verify line count is 455).

If git show is awkward, alternatively read from the design doc reference or earlier commit `05ac7fe`.

**Step 3: Write `preview/src/main.tsx`**

```tsx
import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import 'highlight.js/styles/atom-one-dark.css'
import './index.css'
import App from './App'

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <App />
  </StrictMode>,
)
```

**Step 4: Write placeholder `preview/src/App.tsx`**

```tsx
export default function App() {
  return <div>VERINA — migration in progress</div>
}
```

**Step 5: Verify TypeScript compiles**

```bash
cd preview && pnpm exec tsc -b
```

Expected: no errors.

**Step 6: Verify Vite dev server boots**

```bash
cd preview && timeout 5 pnpm run dev || true
```

Expected: server starts, listens on a port, placeholder renders (manual check not required here — just confirm no crash).

**Step 7: Commit**

```bash
git add preview/index.html preview/src/main.tsx preview/src/index.css preview/src/App.tsx
git commit -m "preview: React shell (index.html, main.tsx, index.css, placeholder App)"
```

---

## Task 3: Shared primitives — utils, hooks, SectionLabel, CodeBlock, bibtex

**Files:**
- Create: `preview/src/lib/utils.ts`, `preview/src/lib/bibtex.ts`, `preview/src/hooks/useStickyNav.ts`, `preview/src/hooks/useScrollReveal.ts`, `preview/src/components/SectionLabel.tsx`, `preview/src/components/CodeBlock.tsx`

**Step 1: `preview/src/lib/utils.ts`**

```ts
import { clsx, type ClassValue } from 'clsx'
import { twMerge } from 'tailwind-merge'

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs))
}
```

**Step 2: `preview/src/lib/bibtex.ts`**

```ts
export const BIBTEX = `@inproceedings{ye2025verina,
  title={VERINA: Benchmarking Verifiable Code Generation},
  author={Ye, Zhe and Yan, Zhengxu and He, Jingxuan and Kasriel, Timothe and Yang, Kaiyu and Song, Dawn},
  booktitle={International Conference on Learning Representations (ICLR)},
  year={2026}
}`
```

**Step 3: `preview/src/hooks/useStickyNav.ts`**

```ts
import { useEffect, useState } from 'react'

export function useStickyNav(threshold = 40) {
  const [scrolled, setScrolled] = useState(() =>
    typeof window !== 'undefined' && window.scrollY > threshold
  )

  useEffect(() => {
    const onScroll = () => setScrolled(window.scrollY > threshold)
    window.addEventListener('scroll', onScroll, { passive: true })
    onScroll()
    return () => window.removeEventListener('scroll', onScroll)
  }, [threshold])

  return scrolled
}
```

**Step 4: `preview/src/hooks/useScrollReveal.ts`**

```ts
import { useEffect } from 'react'

export function useScrollReveal(selector = '.reveal') {
  useEffect(() => {
    const elements = document.querySelectorAll(selector)
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) {
          if (entry.isIntersecting) {
            entry.target.classList.add('visible')
            observer.unobserve(entry.target)
          }
        }
      },
      { threshold: 0.08, rootMargin: '0px 0px -40px 0px' }
    )
    elements.forEach((el) => observer.observe(el))
    return () => observer.disconnect()
  }, [selector])
}
```

**Step 5: `preview/src/components/SectionLabel.tsx`**

```tsx
import { cn } from '@/lib/utils'

interface SectionLabelProps {
  children: React.ReactNode
  centered?: boolean
  className?: string
}

export function SectionLabel({ children, centered = false, className }: SectionLabelProps) {
  return (
    <div className={cn('section-label', centered && 'justify-center', className)}>
      {children}
    </div>
  )
}
```

**Step 6: `preview/src/components/CodeBlock.tsx`**

Registers Lean once at module load. Highlights on mount.

```tsx
import { useEffect, useRef } from 'react'
import hljs from 'highlight.js/lib/core'
import bash from 'highlight.js/lib/languages/bash'
// @ts-expect-error - highlightjs-lean has no types
import lean from 'highlightjs-lean'

hljs.registerLanguage('bash', bash)
hljs.registerLanguage('lean', lean)

interface CodeBlockProps {
  language: 'lean' | 'bash'
  code: string
  title?: string
  showChrome?: boolean
  className?: string
}

export function CodeBlock({ language, code, title, showChrome = true, className }: CodeBlockProps) {
  const ref = useRef<HTMLElement>(null)

  useEffect(() => {
    if (ref.current && !ref.current.dataset.highlighted) {
      hljs.highlightElement(ref.current)
    }
  }, [code])

  return (
    <div className={`code-block ${className ?? ''}`}>
      {showChrome && (
        <div className="code-block-header">
          <div className="code-block-dot"></div>
          <div className="code-block-dot"></div>
          <div className="code-block-dot"></div>
          {title && <span className="code-block-title">{title}</span>}
        </div>
      )}
      <pre>
        <code ref={ref} className={`language-${language}`}>
          {code}
        </code>
      </pre>
    </div>
  )
}
```

Note: if `highlightjs-lean` doesn't default-export a function consumable by `registerLanguage`, fall back to the CDN approach by re-adding the `<script>` tag in `index.html` and calling `window.hljs.highlightElement` with a `declare global { interface Window { hljs: any } }` shim. Decide at implementation time by inspecting the package's `main` export.

**Step 7: Verify TypeScript compiles**

```bash
cd preview && pnpm exec tsc -b
```

Expected: no errors.

**Step 8: Commit**

```bash
git add preview/src/lib preview/src/hooks preview/src/components/SectionLabel.tsx preview/src/components/CodeBlock.tsx
git commit -m "preview: shared hooks, utils, SectionLabel, CodeBlock"
```

---

## Task 4: Section components — Nav, Hero, InfoStrip

**Files:**
- Create: `preview/src/components/Nav.tsx`, `preview/src/components/Hero.tsx`, `preview/src/components/InfoStrip.tsx`

Each component ports the corresponding section of `preview/index.html` verbatim (converting `class` → `className`, self-closing tags, escaping `&middot;` etc. as JSX entities or Unicode) and wraps in `export default function X()`.

**Key conversions:**
- `class="..."` → `className="..."`
- `&middot;` → `{'·'}` or literal `·`
- `&mdash;` → `{'\u2014'}` or `—`
- `&amp;` → `&`
- `&lt;` in code (inside `CodeBlock`) → keep as `<` in the string literal
- Inline `onclick="copyBibtex()"` → handled locally in `Citation` (Task 7) with `useState`
- SVG `fill-rule`, `clip-rule` → `fillRule`, `clipRule`
- HTML comments `<!-- ... -->` → `{/* ... */}`

**Step 1: `Nav.tsx`** — port `preview/index.html:39-49`. Use `useStickyNav()` and apply `cn('nav', scrolled && 'scrolled')`.

```tsx
import { cn } from '@/lib/utils'
import { useStickyNav } from '@/hooks/useStickyNav'

export function Nav() {
  const scrolled = useStickyNav()
  return (
    <nav className={cn('nav', scrolled && 'scrolled')}>
      <div className="max-w-6xl mx-auto px-6 h-14 flex items-center justify-between">
        <a href="#" className="nav-logo">VERINA</a>
        <div className="hidden md:flex items-center gap-6">
          <a href="#overview" className="nav-link">Overview</a>
          <a href="#results" className="nav-link">Results</a>
          <a href="#get-started" className="nav-link">Get Started</a>
          <a href="#citation" className="nav-link">Cite</a>
        </div>
      </div>
    </nav>
  )
}
```

**Step 2: `Hero.tsx`** — port `preview/index.html:52-95`. The two inline SVGs (GitHub icon, HF icon) go inline; extract author links into a data array if it improves readability, otherwise inline. Inline.

**Step 3: `InfoStrip.tsx`** — port `preview/index.html:98-119`.

**Step 4: `tsc -b` then commit.**

```bash
cd preview && pnpm exec tsc -b
git add preview/src/components/Nav.tsx preview/src/components/Hero.tsx preview/src/components/InfoStrip.tsx
git commit -m "preview: Nav, Hero, InfoStrip components"
```

---

## Task 5: Section components — Abstract, Overview, Features

**Files:** `Abstract.tsx`, `Overview.tsx`, `Features.tsx` in `preview/src/components/`

Port:
- `Abstract.tsx` ← `preview/index.html:122-131` + the `<div class="section-divider">` at L133
- `Overview.tsx` ← `preview/index.html:136-185`
- `Features.tsx` ← `preview/index.html:188-229`

Each section uses `<SectionLabel>` where appropriate (replaces `<div class="section-label">...</div>`). Images referenced as `images/xxx.png` (relative to root — `vite.config.ts` `base` handles the prefix).

`tsc -b`, commit as `preview: Abstract, Overview, Features components`.

---

## Task 6: Section components — DataFormat, SpecEval, Statistics

**Files:** `DataFormat.tsx`, `SpecEval.tsx`, `Statistics.tsx`

- `DataFormat.tsx` ← `preview/index.html:232-280`. The big Lean code block uses `<CodeBlock language="lean" title="example.lean" code={LEAN_EXAMPLE} />` — define `LEAN_EXAMPLE` as a template literal at the top of the file. Note: `&lt;` in the source HTML must become literal `<` in the string.
- `SpecEval.tsx` ← `preview/index.html:283-316`
- `Statistics.tsx` ← `preview/index.html:319-343` (contains the data table)

`tsc -b`, commit as `preview: DataFormat, SpecEval, Statistics components`.

---

## Task 7: Section components — Results, Combinations, GetStarted, Citation, Acknowledgements, Footer

**Files:** `Results.tsx`, `Combinations.tsx`, `GetStarted.tsx`, `Citation.tsx`, `Acknowledgements.tsx`, `Footer.tsx`

- `Results.tsx` ← `preview/index.html:346-457` (large — 5 result panels)
- `Combinations.tsx` ← `preview/index.html:460-519`
- `GetStarted.tsx` ← `preview/index.html:522-577`. The bash install snippet uses `<CodeBlock language="bash" showChrome={false} code={...} />` — or with chrome; match original (original has no chrome bar, just a plain `code-block` wrapper with `pre`/`code`). Decide by diff'ing current render.
- `Citation.tsx` ← `preview/index.html:580-596`. Replace inline `onclick="copyBibtex()"` with local `useState` + `navigator.clipboard.writeText(BIBTEX)`. Button flips to "Copied!" for 2s.

  ```tsx
  import { useState } from 'react'
  import { BIBTEX } from '@/lib/bibtex'
  import { SectionLabel } from './SectionLabel'

  export function Citation() {
    const [copied, setCopied] = useState(false)
    const handleCopy = async () => {
      try {
        await navigator.clipboard.writeText(BIBTEX)
      } catch {
        // fallback
        const ta = document.createElement('textarea')
        ta.value = BIBTEX
        document.body.appendChild(ta)
        ta.select()
        document.execCommand('copy')
        document.body.removeChild(ta)
      }
      setCopied(true)
      setTimeout(() => setCopied(false), 2000)
    }
    return (
      <section className="py-16 md:py-20 px-6" id="citation">
        <div className="max-w-2xl mx-auto reveal">
          <div className="text-center mb-6">
            <SectionLabel centered>Reference</SectionLabel>
            <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Citation</h2>
          </div>
          <div className="bibtex-block">
            <button className="copy-btn" onClick={handleCopy}>
              {copied ? 'Copied!' : 'Copy'}
            </button>
            <pre><code>{BIBTEX}</code></pre>
          </div>
        </div>
      </section>
    )
  }
  ```

- `Acknowledgements.tsx` ← `preview/index.html:599-613`
- `Footer.tsx` ← `preview/index.html:616-621`

`tsc -b`, commit as `preview: Results, Combinations, GetStarted, Citation, Ack, Footer components`.

---

## Task 8: Compose `App.tsx` + wire scroll-reveal

**File:** `preview/src/App.tsx` (overwrite placeholder)

```tsx
import { useScrollReveal } from '@/hooks/useScrollReveal'
import { Nav } from '@/components/Nav'
import { Hero } from '@/components/Hero'
import { InfoStrip } from '@/components/InfoStrip'
import { Abstract } from '@/components/Abstract'
import { Overview } from '@/components/Overview'
import { Features } from '@/components/Features'
import { DataFormat } from '@/components/DataFormat'
import { SpecEval } from '@/components/SpecEval'
import { Statistics } from '@/components/Statistics'
import { Results } from '@/components/Results'
import { Combinations } from '@/components/Combinations'
import { GetStarted } from '@/components/GetStarted'
import { Citation } from '@/components/Citation'
import { Acknowledgements } from '@/components/Acknowledgements'
import { Footer } from '@/components/Footer'

export default function App() {
  useScrollReveal()
  return (
    <>
      <Nav />
      <Hero />
      <InfoStrip />
      <Abstract />
      <Overview />
      <Features />
      <DataFormat />
      <SpecEval />
      <Statistics />
      <Results />
      <Combinations />
      <GetStarted />
      <Citation />
      <Acknowledgements />
      <Footer />
    </>
  )
}
```

Note: section components export as named exports (e.g. `export function Hero`). If any was authored as `export default` adjust imports accordingly — pick one convention and stick to it. This plan uses **named exports** for all section components (`export function X`) except `App` which is default (matches verisyn).

**Step 1: `tsc -b`** — expect zero errors.

**Step 2: `pnpm run build`** — expect successful bundle; verify `dist/index.html` exists.

**Step 3: Commit** as `preview: wire App.tsx with all sections`.

---

## Task 9: Final verification + start dev server

**Step 1: Build**

```bash
cd preview && pnpm run build
```

Expected: `tsc -b` passes, `vite build` completes, `dist/` contains `index.html`, `assets/`, `images/`.

**Step 2: Start dev server in background**

```bash
cd preview && pnpm run dev
```

Expected: Vite reports `Local: http://localhost:5173/preview/`.

**Step 3: Report URL to user and list sections to eyeball:**

- Nav (translucent on hero, opaque on scroll)
- Hero (gradient, badge, authors, three buttons)
- Info strip (4 stat numbers)
- Abstract, Overview (3 cards), Features (4 cards)
- Data Format (Lean code block with syntax highlighting — **critical smoke check**)
- Spec Eval (figure + 2 cards)
- Statistics (table)
- Results (5 result panels with figures)
- Combinations (3 cards + result panel)
- Get Started (3 numbered steps + bash snippet)
- Citation (BibTeX block with Copy button — **critical smoke check**)
- Acknowledgements, Footer

Scroll-reveal: sections should fade in as they enter the viewport.

---

## Execution notes

- If `highlightjs-lean` fails at `import lean from 'highlightjs-lean'` (wrong export shape), inspect `node_modules/highlightjs-lean/` for the actual entry point — may require `import lean from 'highlightjs-lean/dist/lean.min.js'` or keeping the CDN `<script>` and using `window.hljs`. Decide and adjust in Task 3 Step 6 before moving on.
- If any component's markup produces visible layout drift vs. the current site, diff its JSX against the original HTML line range and fix. Do not "improve" the markup — parity is the goal.
- Commit frequently. Every task ends in a commit.
