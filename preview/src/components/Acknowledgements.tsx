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

function Row({ entry, accent }: { entry: Entry; accent: string }) {
  const name = entry.href ? (
    <a
      href={entry.href}
      target="_blank"
      className="hover:text-blue-600 transition-colors inline-flex items-center gap-1 group"
    >
      {entry.name}
      <span className="text-[10px] text-gray-300 group-hover:text-blue-400 transition-colors">↗</span>
    </a>
  ) : (
    <span>{entry.name}</span>
  )
  return (
    <li className={`flex items-baseline gap-3 py-1.5 pl-3 border-l-2 ${accent}`}>
      <span className="font-display text-sm font-semibold text-gray-800 shrink-0">{name}</span>
      {entry.affiliation && (
        <span className="text-[13px] text-gray-500 italic truncate">{entry.affiliation}</span>
      )}
    </li>
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

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto mb-10">
          We are grateful to the following organizations and individuals &mdash; listed in the order
          of their first contribution &mdash; for improving VERINA's quality through bug reports,
          specification and proof fixes, and other corrections.
        </p>

        <div className="grid md:grid-cols-[auto_1fr] gap-x-10 gap-y-8 mb-8 max-w-xl mx-auto md:max-w-none">
          {/* Organizations column */}
          <div>
            <div className="text-[10px] font-bold text-blue-600 uppercase tracking-[0.14em] mb-3">
              Organizations
            </div>
            <ul className="list-none space-y-0.5 md:min-w-[220px]">
              {ORGANIZATIONS.map((o) => (
                <Row key={o.name} entry={o} accent="border-blue-400/60" />
              ))}
            </ul>
          </div>

          {/* Individuals column */}
          <div>
            <div className="text-[10px] font-bold text-indigo-600 uppercase tracking-[0.14em] mb-3">
              Individuals
            </div>
            <ul className="list-none space-y-0.5">
              {INDIVIDUALS.map((p) => (
                <Row key={p.name} entry={p} accent="border-indigo-400/60" />
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
