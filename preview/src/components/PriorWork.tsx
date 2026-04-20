import { SectionLabel } from './SectionLabel'

type Support = 'full' | 'partial' | 'none'
type Comp = 'yes' | 'no' | 'na'

interface Row {
  name: string
  cite?: string
  code: Support
  spec: Support
  proof: Support
  style: 'ATP' | 'ITP' | null
  comp: Comp
  language: string
}

const BENCHMARKS: Row[] = [
  { name: 'HumanEval',       cite: 'Chen et al., 2021',       code: 'full',    spec: 'none', proof: 'none', style: null,  comp: 'na', language: 'Python' },
  { name: 'MBPP',            cite: 'Austin et al., 2021',     code: 'full',    spec: 'none', proof: 'none', style: null,  comp: 'na', language: 'Python' },
  { name: 'Dafny-Synthesis', cite: 'Misu et al., 2024',       code: 'partial', spec: 'none', proof: 'full', style: 'ATP', comp: 'no', language: 'Dafny' },
  { name: 'DafnyBench',      cite: 'Loughridge et al., 2025', code: 'none',    spec: 'none', proof: 'full', style: 'ATP', comp: 'na', language: 'Dafny' },
  { name: 'miniCodeProps',   cite: 'Lohn & Welleck, 2024',    code: 'none',    spec: 'none', proof: 'full', style: 'ITP', comp: 'na', language: 'Lean' },
  { name: 'FV APPS',         cite: 'Dougherty & Mehta, 2025', code: 'full',    spec: 'partial', proof: 'full', style: 'ITP', comp: 'no', language: 'Lean' },
  { name: 'Clover',          cite: 'Sun et al., 2024',        code: 'full',    spec: 'full', proof: 'full', style: 'ATP', comp: 'no', language: 'Dafny' },
  { name: 'CLEVER',          cite: 'Thakur et al., 2025',     code: 'partial', spec: 'full', proof: 'none', style: null,  comp: 'no', language: 'Lean' },
]

const VERINA: Row = {
  name: 'VERINA', code: 'full', spec: 'full', proof: 'full', style: 'ITP', comp: 'yes', language: 'Lean',
}

function dot(level: Support) {
  if (level === 'full')    return <span className="text-blue-600 font-bold">●</span>
  if (level === 'partial') return <span className="text-gray-400 font-bold">◐</span>
  return <span className="text-gray-200 font-bold">○</span>
}

function comp(c: Comp) {
  if (c === 'yes') return <span className="text-blue-600 font-bold">✓</span>
  if (c === 'no')  return <span className="text-gray-400">✗</span>
  return <span className="text-gray-300">—</span>
}

function Line({ row, highlight = false }: { row: Row; highlight?: boolean }) {
  return (
    <tr className={highlight ? 'bg-blue-50/60 font-semibold' : ''}>
      <td>
        {row.name}
        {row.cite && <span className="block text-[10px] text-gray-400 font-normal italic">{row.cite}</span>}
      </td>
      <td className="text-center">{dot(row.code)}</td>
      <td className="text-center">{dot(row.spec)}</td>
      <td className="text-center">{dot(row.proof)}</td>
      <td className="text-center text-xs">{row.style ?? '—'}</td>
      <td className="text-center">{comp(row.comp)}</td>
      <td className="text-center text-xs">{row.language}</td>
    </tr>
  )
}

export function PriorWork() {
  return (
    <section className="py-16 md:py-20 px-6" id="prior-work">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Comparison</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">VERINA vs. Prior Work</h2>
          <p className="text-sm text-gray-500 max-w-lg mx-auto mt-3 leading-relaxed">
            VERINA is the only benchmark to support all three foundational tasks with full compositionality in Lean.
          </p>
        </div>

        <div className="overflow-x-auto">
          <table className="data-table">
            <thead>
              <tr>
                <th>Work</th>
                <th className="text-center">Code</th>
                <th className="text-center">Spec</th>
                <th className="text-center">Proof</th>
                <th className="text-center">Style</th>
                <th className="text-center">Comp.</th>
                <th className="text-center">Lang</th>
              </tr>
            </thead>
            <tbody>
              {BENCHMARKS.map((r) => (
                <Line key={r.name} row={r} />
              ))}
              <Line row={VERINA} highlight />
            </tbody>
          </table>
        </div>
        <p className="text-[11px] text-gray-400 text-center mt-3">
          ● full · ◐ partial · ○ unsupported. ATP = automated theorem proving, ITP = interactive. Comp. = modular compositionality across tasks.
        </p>
      </div>
    </section>
  )
}
