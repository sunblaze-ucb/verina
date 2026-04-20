import { SectionLabel } from './SectionLabel'

const SOURCES = [
  {
    name: 'MBPP-DFY-50',
    count: 49,
    color: 'text-blue-600',
    origin: 'Misu et al., 2024',
    note: 'MBPP problems paired with human-verified Dafny solutions, manually translated to Lean.',
  },
  {
    name: 'CloverBench',
    count: 59,
    color: 'text-indigo-600',
    origin: 'Sun et al., 2024',
    note: 'Human-authored Dafny instances translated via OpenAI o3-mini with manual correction.',
  },
  {
    name: 'Student submissions',
    count: 81,
    color: 'text-amber-600',
    origin: 'UC Berkeley theorem-proving course',
    note: 'Formalized in Lean by students, sourced from LeetCode and LiveCodeBench; reviewed and edited by authors.',
  },
]

export function Abstract() {
  return (
    <>
      <section className="py-16 md:py-20 px-6" id="abstract">
        <div className="max-w-3xl mx-auto reveal">
          <SectionLabel>Abstract</SectionLabel>
          <div className="text-[15px] md:text-base leading-[1.8] text-gray-600 max-w-2xl">
            <p>
              Large language models (LLMs) are increasingly integrated in software development, but ensuring correctness in LLM-generated code remains challenging. <strong className="text-gray-800">Verifiable code generation</strong>—jointly generating code, specifications, and proofs of code-specification alignment—offers a promising path forward. We introduce <strong className="text-gray-800">VERINA</strong>, a high-quality benchmark enabling comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions. VERINA consists of <strong className="text-gray-800">189 manually curated coding tasks</strong> in Lean with detailed problem descriptions, reference implementations, formal specifications, and extensive test suites. The best model, OpenAI o3, achieves <strong className="text-gray-800">72.6% code correctness, 52.3% specification soundness &amp; completeness, and only 4.9% proof success</strong>—revealing that proof generation remains a critical bottleneck.
            </p>
          </div>

          <div className="mt-10">
            <div className="text-xs font-bold text-gray-400 uppercase tracking-wider mb-3">Data sources</div>
            <div className="grid sm:grid-cols-3 gap-4">
              {SOURCES.map(({ name, count, color, origin, note }) => (
                <div key={name} className="card p-5">
                  <div className={`font-display text-3xl font-extrabold tracking-tight tabular-nums leading-none ${color}`}>{count}</div>
                  <div className="font-display text-sm font-bold mt-2">{name}</div>
                  <div className="text-[11px] text-gray-400 italic mb-1.5">{origin}</div>
                  <p className="text-xs text-gray-500 leading-relaxed">{note}</p>
                </div>
              ))}
            </div>
          </div>
        </div>
      </section>
      <div className="section-divider"></div>
    </>
  )
}
