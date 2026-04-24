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

        {/* Spec evaluator diagram — wrapped in result-panel like the figures
            in the Results section; image height-capped so the container
            never dominates the column */}
        <div className="result-panel mb-10">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Evaluator Pipeline</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img
                src="images/verina_cropped_06.png"
                alt="Specification evaluation framework"
                className="max-h-72 md:max-h-80 w-auto"
              />
            </div>
            <p className="fig-caption">
              Testing-based evaluator for specification soundness and completeness.
            </p>
          </div>
        </div>

        <div className="grid md:grid-cols-2 gap-4 mb-10">
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

        {/* Closer takeaway — styled distinctively from the insight-box used
            in Why VERINA: teal-accented card that visually echoes the
            Soundness swatch above, with a small "takeaway" eyebrow */}
        <div className="relative rounded-[10px] border border-teal-200/70 bg-gradient-to-br from-teal-50/80 to-white border-l-[3px] border-l-teal-500 p-6 md:p-7">
          <div className="text-[10px] font-bold text-teal-700 uppercase tracking-[0.14em] mb-2">
            Takeaway
          </div>
          <p className="text-sm md:text-[15px] text-gray-700 leading-[1.8]">
            Our framework leverages <strong className="text-gray-900">comprehensive test suites</strong> and <strong className="text-gray-900">Lean's property-based testing</strong> to systematically evaluate these relationships, providing robust automatic assessment of specification quality without requiring manual proof construction.
          </p>
        </div>
      </div>
    </section>
  )
}
