import { SectionLabel } from './SectionLabel'
import { SiGithub } from 'react-icons/si'

interface Entry {
  name: string
  affiliation?: string
  href?: string
}

// Within each group: order of first contribution.
const ORGANIZATIONS: Entry[] = [
  { name: 'Harmonic',             href: 'https://harmonic.fun/' },
  { name: 'Logical Intelligence', href: 'https://logicalintelligence.com/' },
]

const INDIVIDUALS: Entry[] = [
  { name: 'Mantas Baksys', affiliation: 'University of Cambridge' },
  { name: 'Yueyang Feng',  affiliation: 'National University of Singapore' },
  { name: 'Dipesh Kafle',  affiliation: 'National University of Singapore' },
  { name: 'Ilya Sergey',   affiliation: 'National University of Singapore' },
]

function LinkedName({ entry }: { entry: Entry }) {
  if (!entry.href) return <>{entry.name}</>
  return (
    <a href={entry.href} target="_blank" className="hover:text-blue-600 transition-colors">
      {entry.name}
    </a>
  )
}

export function Acknowledgements() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="acknowledgements">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Credits</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Acknowledgements</h2>
        </div>

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto mb-8">
          We are grateful to the following organizations and individuals &mdash; listed in the order
          of their first contribution &mdash; for improving VERINA's quality through bug reports,
          specification and proof fixes, and other corrections.
        </p>

        <div className="card p-6 md:p-7 mb-6">
          <div className="mb-6">
            <div className="text-[10px] font-bold text-blue-600 uppercase tracking-[0.14em] mb-2">
              Organizations
            </div>
            <p className="text-sm md:text-[15px] text-gray-700 leading-[1.8]">
              {ORGANIZATIONS.map((o, i) => (
                <span key={o.name}>
                  <LinkedName entry={o} />
                  {i < ORGANIZATIONS.length - 1 && <span className="mx-2 text-gray-300">·</span>}
                </span>
              ))}
            </p>
          </div>

          <div>
            <div className="text-[10px] font-bold text-indigo-600 uppercase tracking-[0.14em] mb-2">
              Individuals
            </div>
            <ul className="text-sm md:text-[15px] text-gray-700 leading-[1.9] space-y-0.5 list-none">
              {INDIVIDUALS.map((p) => (
                <li key={p.name}>
                  <LinkedName entry={p} />
                  {p.affiliation && (
                    <span className="text-gray-500 italic">
                      {' '}&mdash; {p.affiliation}
                    </span>
                  )}
                </li>
              ))}
            </ul>
          </div>
        </div>

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
