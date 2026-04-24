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

const PEOPLE: Entry[] = [
  { name: 'Mantas Baksys', affiliation: 'University of Cambridge' },
  { name: 'Yueyang Feng',  affiliation: 'National University of Singapore' },
  { name: 'Dipesh Kafle',  affiliation: 'National University of Singapore' },
  { name: 'Ilya Sergey',   affiliation: 'National University of Singapore' },
]

function Entry({ entry }: { entry: Entry }) {
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
    entry.name
  )
  return (
    <li className="text-center">
      <div className="font-display text-[15px] font-semibold text-gray-800">{name}</div>
      {entry.affiliation && (
        <div className="text-[12px] text-gray-500 italic mt-0.5">{entry.affiliation}</div>
      )}
    </li>
  )
}

export function Acknowledgements() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="acknowledgements">
      <div className="max-w-3xl mx-auto reveal text-center">
        <SectionLabel centered>Credits</SectionLabel>
        <h2 className="font-display text-2xl md:text-3xl font-bold mt-1 mb-6">Acknowledgements</h2>

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] max-w-2xl mx-auto mb-12">
          We are grateful to the following organizations and people &mdash; listed in the order of
          their first contribution &mdash; for improving VERINA's quality through bug reports,
          specification and proof fixes, and other corrections.
        </p>

        <div className="mb-10">
          <div className="text-[10px] font-bold text-blue-600 uppercase tracking-[0.16em] mb-4">
            Organizations
          </div>
          <ul className="list-none space-y-3">
            {ORGANIZATIONS.map((o) => (
              <Entry key={o.name} entry={o} />
            ))}
          </ul>
        </div>

        <div className="flex items-center justify-center mb-10">
          <div className="h-px w-16 bg-gray-200"></div>
        </div>

        <div className="mb-10">
          <div className="text-[10px] font-bold text-indigo-600 uppercase tracking-[0.16em] mb-4">
            People
          </div>
          <ul className="list-none space-y-3">
            {PEOPLE.map((p) => (
              <Entry key={p.name} entry={p} />
            ))}
          </ul>
        </div>

        <p className="text-xs text-gray-500 leading-relaxed">
          Also see the list of contributors on the{' '}
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
