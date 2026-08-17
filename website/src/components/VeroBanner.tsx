import { LuArrowUpRight } from 'react-icons/lu'

export function VeroBanner() {
  return (
    <aside className="vero-banner-wrap" aria-label="Explore Vero">
      <a
        className="vero-banner"
        href="https://vero.verina.io"
        target="_blank"
        rel="noopener noreferrer"
      >
        <span className="vero-mark" aria-hidden="true">
          <svg viewBox="0 0 32 32" role="img">
            <path d="M4 17 L12.5 25.5 L28 7" />
          </svg>
        </span>

        <span className="vero-copy">
          <span className="vero-kicker">
            <span>New</span>
            From the VERINA team
          </span>
          <span className="vero-title">Interested in repository-level benchmarks?</span>
          <span className="vero-description">
            Meet Vero, where agents build formally verified software across complete,
            multi-module Lean 4 projects.
          </span>
        </span>

        <span className="vero-cta">
          Explore Vero
          <LuArrowUpRight aria-hidden="true" />
        </span>
      </a>
    </aside>
  )
}
