import { SectionLabel } from './SectionLabel'

export function SpecEval() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="spec-eval">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Metrics</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Specification Evaluation Framework</h2>
        </div>

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto mb-8">
          VERINA introduces a novel automated evaluation framework for model-generated specifications, assessing their <strong className="text-gray-800">soundness</strong> and <strong className="text-gray-800">completeness</strong> with respect to ground truth specifications through comprehensive testing.
        </p>

        <div className="img-container mb-3">
          <img
            src="images/verina_cropped_06.png"
            alt="Specification evaluation framework"
            className="w-full max-w-[240px] md:max-w-[280px] h-auto"
          />
        </div>
        <p className="fig-caption mb-10">
          Testing-based evaluator for specification soundness and completeness.
        </p>

        <div className="grid md:grid-cols-2 gap-4 mb-8">
          <div className="card p-5 border-l-3 border-l-teal-500">
            <h3 className="font-display text-sm font-bold text-teal-700 mb-1">Soundness</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              The specification only accepts correct programs. Pre-condition: ground truth implies generated. Post-condition: generated implies ground truth.
            </p>
          </div>
          <div className="card p-5 border-l-3 border-l-blue-500">
            <h3 className="font-display text-sm font-bold text-blue-700 mb-1">Completeness</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              The specification accepts all correct programs. Pre-condition: generated implies ground truth. Post-condition: ground truth implies generated.
            </p>
          </div>
        </div>

        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto">
          Our framework leverages comprehensive test suites and Lean's property-based testing to systematically evaluate these relationships, providing robust automatic assessment of specification quality without requiring manual proof construction.
        </p>
      </div>
    </section>
  )
}
