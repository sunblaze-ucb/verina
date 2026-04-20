import { SectionLabel } from './SectionLabel'

export function Combinations() {
  return (
    <section className="py-16 md:py-20 px-6" id="combinations">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Compositionality</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Task Combinations</h2>
          <p className="text-sm text-gray-500 max-w-lg mx-auto mt-3 leading-relaxed">
            VERINA's modular design supports diverse real-world workflows by composing foundational tasks.
          </p>
        </div>

        <div className="grid md:grid-cols-3 gap-4 mb-8">
          <div className="card p-5 text-center">
            <div className="img-container h-24 mb-3">
              <img src="images/verina_cropped_03.png" alt="Spec-guided code gen" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-xs font-bold mb-1">Spec-Guided CodeGen</h3>
            <p className="text-[11px] text-gray-500 leading-relaxed">
              Generate code from a description + specification, then prove correctness.
            </p>
          </div>

          <div className="card p-5 text-center">
            <div className="img-container h-24 mb-3">
              <img src="images/verina_cropped_04.png" alt="Spec inference from code" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-xs font-bold mb-1">Spec Inference</h3>
            <p className="text-[11px] text-gray-500 leading-relaxed">
              Annotate existing code with formal specifications and prove alignment.
            </p>
          </div>

          <div className="card p-5 text-center">
            <div className="img-container h-24 mb-3">
              <img src="images/verina_cropped_05.png" alt="End-to-end generation" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-xs font-bold mb-1">End-to-End</h3>
            <p className="text-[11px] text-gray-500 leading-relaxed">
              From description alone, independently generate code, specs, and proofs.
            </p>
          </div>
        </div>

        {/* Contextual impact chart */}
        <div className="result-panel">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Impact of Contextual Information</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/combined_task_pass1_00.png" alt="Contextual information impact" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">Providing ground truth specification consistently improves CodeGen; code context has minimal impact on SpecGen.</p>
          </div>
        </div>
      </div>
    </section>
  )
}
