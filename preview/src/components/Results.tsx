import { SectionLabel } from './SectionLabel'

export function Results() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="results">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Evaluation</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Key Results</h2>
          <p className="text-sm text-gray-500 max-w-lg mx-auto mt-3 leading-relaxed">
            We evaluated 10 general-purpose LLMs and 3 specialized provers. Proof generation remains a critical open challenge.
          </p>
        </div>

        {/* Best results strip */}
        <div className="grid grid-cols-3 gap-3 mb-10">
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

        <p className="text-center text-xs text-gray-400 -mt-6 mb-8">Best pass@1 scores (OpenAI o3)</p>

        {/* Foundational tasks */}
        <div className="result-panel mb-6">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Foundational Task Performance</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/foundation_task_pass1_00.png" alt="Foundational task results" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">pass@1 on CodeGen, SpecGen, and ProofGen across 10 LLMs.</p>
          </div>
        </div>

        <div className="insight-box mb-8 text-xs text-gray-600 leading-relaxed">
          A clear difficulty hierarchy emerges: code generation is most accessible, specification generation moderately challenging, and proof generation extremely difficult for all current models.
        </div>

        {/* VERINA-A vs VERINA-B */}
        <div className="result-panel mb-6">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Difficulty Split: VERINA-A vs VERINA-B</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/foundation_task_pass1_split_00.png" alt="VERINA-A vs VERINA-B comparison" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">Substantial performance drops on VERINA-B (student-written) across all tasks.</p>
          </div>
        </div>

        {/* End-to-end */}
        <div className="result-panel mb-6">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">End-to-End Verifiable Code Generation</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-500 mb-4 leading-relaxed">
              ProofGen is the bottleneck: o3 achieves 41.2% Code&amp;Spec Score but only 3.2% End-to-End Score.
            </p>
            <div className="img-container">
              <div className="fig-placeholder max-w-xl mx-auto">Figure 6: End-to-end scores (Code&amp;Spec + End-to-End)</div>
            </div>
            <p className="fig-caption">pass@1 on the end-to-end verifiable code generation task.</p>
          </div>
        </div>

        {/* Specialized provers */}
        <div className="result-panel mb-6">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Specialized Provers &amp; Agentic Methods</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-500 mb-4 leading-relaxed">
              Specialized provers (Goedel Prover V2, DeepSeek Prover V2) and agentic frameworks (Copra) outperform general-purpose models on ProofGen.
            </p>
            <div className="img-container">
              <div className="fig-placeholder max-w-md mx-auto">Figure 7: ProofGen pass@1 across provers</div>
            </div>
            <p className="fig-caption">Comparison of general-purpose models, specialized provers, and agentic approaches.</p>
          </div>
        </div>

        {/* Proof refinement */}
        <div className="result-panel">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Iterative Proof Refinement</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-500 mb-4 leading-relaxed">
              Using Lean compiler feedback iteratively improves proof success, but rates remain low—highlighting persistent challenges in automated theorem proving.
            </p>
            <div className="img-container">
              <img src="images/proof_refine_pass_00.png" alt="Proof refinement results" className="max-w-lg w-full" />
            </div>
            <p className="fig-caption">pass@k via iterative refinement (left) and direct generation (right).</p>
          </div>
        </div>
      </div>
    </section>
  )
}
