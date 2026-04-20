import { SectionLabel } from './SectionLabel'

export function SpecEval() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="spec-eval">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Metrics</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Specification Evaluation</h2>
          <p className="text-sm text-gray-500 max-w-lg mx-auto mt-3 leading-relaxed">
            VERINA introduces an automated framework that assesses generated specifications along two axes.
          </p>
        </div>

        <div className="img-container mb-4">
          <img src="images/verina_cropped_06.png" alt="Specification evaluation framework" className="max-w-xs w-full" />
        </div>
        <p className="fig-caption mb-8">
          Testing-based evaluator for specification soundness and completeness.
        </p>

        <div className="grid md:grid-cols-2 gap-4">
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
      </div>
    </section>
  )
}
