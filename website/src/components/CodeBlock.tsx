import { useEffect, useRef } from 'react'
import hljs from 'highlight.js/lib/core'
import bash from 'highlight.js/lib/languages/bash'
// @ts-expect-error highlightjs-lean ships no type definitions
import * as leanModule from 'highlightjs-lean'

// highlightjs-lean uses `module.exports = function(hljs)`. Vite's CJS→ESM
// interop sometimes surfaces that as `.default`, sometimes as the namespace
// itself. Accept either.
const lean =
  typeof leanModule === 'function'
    ? (leanModule as unknown as (hljs: typeof import('highlight.js').default) => unknown)
    : ((leanModule as { default?: unknown }).default as (
        hljs: typeof import('highlight.js').default,
      ) => unknown)

if (!hljs.getLanguage('bash')) hljs.registerLanguage('bash', bash)
if (!hljs.getLanguage('lean')) hljs.registerLanguage('lean', lean as Parameters<typeof hljs.registerLanguage>[1])

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
