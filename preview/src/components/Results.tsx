import { SectionLabel } from './SectionLabel'

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
        <div className="result-panel mb-6">
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

        {/* Best Results — mirrors docs/ info-light box */}
        <div className="insight-box mb-8">
          <h4 className="font-display text-sm font-bold text-blue-700 mb-3">Best Results (OpenAI o4-mini)</h4>
          <div className="grid grid-cols-3 gap-3 mb-3">
            <div className="stat-card bg-green-50 border border-green-200">
              <div className="stat-value text-green-600">61.4%</div>
              <div className="stat-label text-green-700">Code</div>
            </div>
            <div className="stat-card bg-amber-50 border border-amber-200">
              <div className="stat-value text-amber-600">51.0%</div>
              <div className="stat-label text-amber-700">Spec</div>
            </div>
            <div className="stat-card bg-red-50 border border-red-200">
              <div className="stat-value text-red-600">3.6%</div>
              <div className="stat-label text-red-700">Proof</div>
            </div>
          </div>
          <p className="text-xs text-gray-600 leading-relaxed">
            Results show a clear difficulty hierarchy, with proof generation being the most challenging task for current LLMs.
          </p>
        </div>

        {/* VERINA-A vs VERINA-B chart */}
        <div className="result-panel mb-6">
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

        {/* VERINA-A vs VERINA-B — warning-style box from docs/ */}
        <div className="mb-8 rounded-[10px] border border-amber-200 bg-amber-50/60 border-l-[3px] border-l-amber-500 p-5">
          <p className="text-sm text-gray-700 leading-relaxed">
            <strong className="text-gray-900">VERINA-B vs VERINA-A:</strong> Substantial performance drops across all tasks for more complex problems, highlighting the challenges LLMs face with increased problem complexity.
          </p>
        </div>

        {/* End-to-end Fig 6 — summarized from paper §5 */}
        <div className="result-panel mb-6">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">End-to-End Verifiable Code Generation</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-600 mb-4 leading-relaxed">
              ProofGen is the major bottleneck for end-to-end verifiable code generation. Simultaneously generating correct code and specifications is difficult — the leading model achieves <strong className="text-gray-800">41.2%</strong> on the Code&amp;Spec Score, while the End-to-End Score caps at <strong className="text-gray-800">3.2%</strong> across all evaluated models.
            </p>
            <div className="img-container">
              <img src="images/e2e_pass1.png" alt="End-to-end pass@1 results" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">pass@1 performance on VERINA's end-to-end verifiable code generation task.</p>
          </div>
        </div>

        {/* Specialized provers Fig 7 — summarized from paper §5 */}
        <div className="result-panel mb-8">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Specialized Provers &amp; Agentic Methods</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-600 mb-4 leading-relaxed">
              Specialized theorem-proving models and agentic approaches outperform general-purpose LLMs on ProofGen. <strong className="text-gray-800">Goedel Prover V2 32B</strong> and <strong className="text-gray-800">DeepSeek Prover V2 7B</strong> achieve higher proof success rates; <strong className="text-gray-800">Copra</strong>, a tree-search agent using o4-mini as its backbone with up to 64 LLM queries per sample, also demonstrates clear improvements over direct single-pass generation.
            </p>
            <div className="img-container">
              <img src="images/proof_pass1.png" alt="ProofGen pass@1 across provers" className="max-w-md w-full" />
            </div>
            <p className="fig-caption">pass@1 for ProofGen across general-purpose models, specialized provers, and an agentic framework.</p>
          </div>
        </div>

        {/* Iterative refinement — docs/ text verbatim */}
        <div className="result-panel">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Iterative Refinement Results</h3>
          </div>
          <div className="result-panel-body">
            <p className="text-xs text-gray-600 mb-4 leading-relaxed">
              With 64 iterations of proof refinement using Lean compiler feedback, success rates improved from <strong className="text-gray-800">3.6% to 22.2%</strong> on VERINA-A, but remained low at <strong className="text-gray-800">6.17%</strong> on VERINA-B, highlighting the persistent challenges in automated theorem proving.
            </p>
            <div className="img-container">
              <img src="images/proof_refine_pass_00.png" alt="Proof refinement results" className="max-w-lg w-full" />
            </div>
            <p className="fig-caption">Iterative proof refinement results showing improvement with Lean compiler feedback.</p>
          </div>
        </div>
      </div>
    </section>
  )
}
