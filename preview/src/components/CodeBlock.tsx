import { useEffect, useRef } from 'react'
import hljs from 'highlight.js/lib/core'
import bash from 'highlight.js/lib/languages/bash'
// @ts-expect-error highlightjs-lean ships no type definitions
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
