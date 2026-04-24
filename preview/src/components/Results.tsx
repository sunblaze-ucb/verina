import { SectionLabel } from './SectionLabel'

interface TakeawayProps {
  label: string
  accent?: 'blue' | 'amber' | 'red' | 'teal' | 'indigo'
  children: React.ReactNode
}

const ACCENT_BAR: Record<NonNullable<TakeawayProps['accent']>, string> = {
  blue:   'border-blue-400',
  amber:  'border-amber-400',
  red:    'border-red-400',
  teal:   'border-teal-400',
  indigo: 'border-indigo-400',
}
const ACCENT_TEXT: Record<NonNullable<TakeawayProps['accent']>, string> = {
  blue:   'text-blue-600',
  amber:  'text-amber-700',
  red:    'text-red-600',
  teal:   'text-teal-700',
  indigo: 'text-indigo-600',
}

function Takeaway({ label, accent = 'blue', children }: TakeawayProps) {
  return (
    <div className={`relative my-6 mx-auto max-w-2xl pl-5 border-l-2 ${ACCENT_BAR[accent]}`}>
      <div className={`text-[10px] font-bold uppercase tracking-[0.14em] mb-1.5 ${ACCENT_TEXT[accent]}`}>
        {label}
      </div>
      <p className="text-sm text-gray-600 leading-[1.8]">{children}</p>
    </div>
  )
}

export function Results() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="results">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Evaluation</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Key Evaluation Results</h2>
          <p className="text-sm text-gray-500 max-w-2xl mx-auto mt-3 leading-relaxed">
            We evaluated state-of-the-art LLMs on VERINA's three foundational tasks. Our results reveal significant challenges in verifiable code generation.
          </p>
        </div>

        {/* Foundational tasks */}
        <div className="result-panel mb-4">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Foundational Task Performance</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/foundation_task_pass1_00.png" alt="Foundational task results" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">pass@1 performance of LLMs on VERINA's three foundational tasks.</p>
          </div>
        </div>

        {/* Best pass@1 — standalone stat trio */}
        <div className="mb-2">
          <div className="grid grid-cols-3 gap-3">
            <div className="stat-card bg-green-50 border border-green-200">
              <div className="stat-value text-green-600">72.6%</div>
              <div className="stat-label text-green-700">Code</div>
            </div>
            <div className="stat-card bg-amber-50 border border-amber-200">
              <div className="stat-value text-amber-600">52.3%</div>
              <div className="stat-label text-amber-700">Spec</div>
            </div>
            <div className="stat-card bg-red-50 border border-red-200">
              <div className="stat-value text-red-600">4.9%</div>
              <div className="stat-label text-red-700">Proof</div>
            </div>
          </div>
          <p className="fig-caption mt-2">Best pass@1 scores &mdash; OpenAI o3</p>
        </div>

        <Takeaway label="Takeaway" accent="blue">
          <strong className="text-gray-800">A clear difficulty hierarchy emerges.</strong>{' '}
          Code generation is most accessible, specification generation is moderately challenging,
          and proof generation remains extremely difficult for all current models.
        </Takeaway>

        {/* VERINA-A vs VERINA-B */}
        <div className="result-panel mb-4 mt-10">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Difficulty Split: VERINA-A vs VERINA-B</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/foundation_task_pass1_split_00.png" alt="VERINA-A vs VERINA-B comparison" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">Performance comparison between VERINA-A and VERINA-B.</p>
          </div>
        </div>

        <Takeaway label="Takeaway" accent="amber">
          <strong className="text-gray-800">VERINA-B is substantially harder.</strong>{' '}
          All tasks show steep performance drops on student-written problems, highlighting the
          challenges LLMs face as problem complexity increases.
        </Takeaway>

        {/* End-to-end */}
        <div className="result-panel mb-4 mt-10">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">End-to-End Verifiable Code Generation</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/e2e_pass1.png" alt="End-to-end pass@1 results" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">pass@1 performance on VERINA's end-to-end verifiable code generation task.</p>
          </div>
        </div>

        <Takeaway label="Takeaway" accent="red">
          <strong className="text-gray-800">ProofGen is the end-to-end bottleneck.</strong>{' '}
          Simultaneously generating correct code and specifications is difficult — the leading model
          reaches <strong className="text-gray-800">41.2%</strong> Code&amp;Spec, while the End-to-End
          Score caps at <strong className="text-gray-800">3.2%</strong> across all evaluated models.
        </Takeaway>

        {/* Specialized provers */}
        <div className="result-panel mb-4 mt-10">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Specialized Provers &amp; Agentic Methods</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/proof_pass1.png" alt="ProofGen pass@1 across provers" className="max-w-md w-full" />
            </div>
            <p className="fig-caption">pass@1 for ProofGen across general-purpose models, specialized provers, and an agentic framework.</p>
          </div>
        </div>

        <Takeaway label="Takeaway" accent="teal">
          <strong className="text-gray-800">Specialized provers and agents outperform general-purpose LLMs on ProofGen.</strong>{' '}
          Goedel Prover V2 32B and DeepSeek Prover V2 7B achieve higher proof success rates than the
          best general-purpose models; Copra, a tree-search agent using o4-mini as backbone (up to
          64 queries per sample), also shows clear improvements over single-pass generation.
        </Takeaway>

        {/* Iterative proof refinement */}
        <div className="result-panel mb-4 mt-10">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Iterative Proof Refinement</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/proof_refine_pass_00.png" alt="Proof refinement results" className="max-w-lg w-full" />
            </div>
            <p className="fig-caption">pass@k via iterative refinement (left) and direct generation (right).</p>
          </div>
        </div>

        <Takeaway label="Takeaway" accent="indigo">
          <strong className="text-gray-800">Lean verifier feedback helps.</strong>{' '}
          Iterative proof refinement using Lean compiler errors reliably outperforms direct
          generation at matched query budgets, reaching <strong className="text-gray-800">20.1%
          pass@64</strong>. Refinement yields larger gains on VERINA-A (7.41% → 22.22%) than on
          VERINA-B (1.23% → 6.17%), underscoring the persistent challenge of complex proving tasks.
        </Takeaway>
      </div>
    </section>
  )
}
