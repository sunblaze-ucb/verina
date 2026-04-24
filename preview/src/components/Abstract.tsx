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
          <div className="text-[15px] md:text-base leading-[1.8] text-gray-600 text-justify hyphens-auto [text-align-last:left]">
            <p>
              Large language models (LLMs) are increasingly integrated in software development, but ensuring correctness in LLM-generated code remains challenging and often requires costly manual review. <strong className="text-gray-800">Verifiable code generation</strong>—jointly generating code, specifications, and proofs of code-specification alignment—offers a promising path to address this limitation and further unleash LLMs' benefits in coding. Yet, there exists a significant gap in evaluation: current benchmarks often lack support for end-to-end verifiable code generation. In this paper, we introduce <strong className="text-gray-800">VERINA</strong> (Verifiable Code Generation Arena), a high-quality benchmark enabling a comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions. VERINA consists of <strong className="text-gray-800">189 manually curated coding tasks</strong> in Lean, with detailed problem descriptions, reference implementations, formal specifications, and extensive test suites. Our extensive evaluation of state-of-the-art LLMs reveals significant challenges in verifiable code generation, especially in proof generation, underscoring the need for improving LLM-based theorem provers in verification domains. The best model, OpenAI o4-mini, generates only <strong className="text-gray-800">61.4% correct code, 51.0% sound and complete specifications, and 3.6% successful proofs</strong>, with one trial per task. We hope VERINA will catalyze progress in verifiable code generation by providing a rigorous and comprehensive benchmark.
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
