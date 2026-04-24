import { SectionLabel } from './SectionLabel'
import { SiGithub } from 'react-icons/si'

interface Contributor {
  name: string
  affiliation?: string
  href?: string
}

// Chronological order of contribution.
const CONTRIBUTORS: Contributor[] = [
  { name: 'Harmonic', href: 'https://harmonic.fun/' },
  { name: 'Mantas Baksys', affiliation: 'University of Cambridge' },
  { name: 'Yueyang Feng', affiliation: 'National University of Singapore' },
  { name: 'Dipesh Kafle', affiliation: 'National University of Singapore' },
  { name: 'Ilya Sergey', affiliation: 'National University of Singapore' },
  { name: 'Logical Intelligence', href: 'https://logicalintelligence.com/' },
]

export function Acknowledgements() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="acknowledgements">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Credits</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Acknowledgements</h2>
        </div>

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto mb-8">
          We thank the following people and teams, listed in order of their contribution, for
          reporting bugs, fixing errors in specifications and proofs, and otherwise improving
          VERINA's quality.
        </p>

        {/* Contributors grid — compact, card-style with optional affiliation */}
        <ol className="grid sm:grid-cols-2 md:grid-cols-3 gap-3 mb-6 list-none">
          {CONTRIBUTORS.map((c, i) => (
            <li
              key={c.name}
              className="card p-4 flex gap-3 items-start"
            >
              <span className="font-display text-[11px] font-extrabold text-blue-500/70 tabular-nums tracking-widest mt-0.5 shrink-0">
                {String(i + 1).padStart(2, '0')}
              </span>
              <div className="min-w-0">
                <div className="font-display text-sm font-bold leading-tight">
                  {c.href ? (
                    <a
                      href={c.href}
                      target="_blank"
                      className="hover:text-blue-600 transition-colors"
                    >
                      {c.name}
                    </a>
                  ) : (
                    c.name
                  )}
                </div>
                {c.affiliation && (
                  <div className="text-[11px] text-gray-500 italic mt-0.5 leading-snug">
                    {c.affiliation}
                  </div>
                )}
              </div>
            </li>
          ))}
        </ol>

        <p className="text-xs text-gray-500 text-center leading-relaxed">
          See the full list of code contributors on the{' '}
          <a
            href="https://github.com/sunblaze-ucb/verina/graphs/contributors"
            target="_blank"
            className="inline-flex items-center gap-1 text-blue-600 hover:underline align-baseline"
          >
            <SiGithub className="w-3 h-3" aria-hidden="true" />
            GitHub contributors page
          </a>
          .
        </p>
      </div>
    </section>
  )
}
