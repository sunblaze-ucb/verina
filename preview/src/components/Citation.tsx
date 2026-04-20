import { useState } from 'react'
import { BIBTEX } from '@/lib/bibtex'
import { SectionLabel } from './SectionLabel'

export function Citation() {
  const [copied, setCopied] = useState(false)

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(BIBTEX)
    } catch {
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
          <button className="copy-btn" onClick={handleCopy} type="button">
            {copied ? 'Copied!' : 'Copy'}
          </button>
          <pre><code>{BIBTEX}</code></pre>
        </div>
      </div>
    </section>
  )
}
