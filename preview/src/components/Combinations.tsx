import { SectionLabel } from './SectionLabel'

export function Combinations() {
  return (
    <section className="py-16 md:py-20 px-6" id="combinations">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Compositionality</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Supported Task Combinations</h2>
          <p className="text-sm text-gray-500 max-w-xl mx-auto mt-3 leading-relaxed">
            VERINA's modular design enables evaluation of various real-world scenarios in verifiable code generation.
          </p>
        </div>

        {/* First two combinations — 2-col */}
        <div className="grid md:grid-cols-2 gap-4 mb-4">
          <div className="card p-6 text-center">
            <div className="img-container h-28 mb-4">
              <img src="images/verina_cropped_03.png" alt="Spec-guided code generation" className="max-h-full w-auto max-w-[300px]" />
            </div>
            <h3 className="font-display text-sm font-bold mb-1.5">Specification-Guided Code Generation</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Given a natural language description and formal specification, generate code and prove its correctness. This scenario reflects development workflows where specifications are available upfront.
            </p>
          </div>

          <div className="card p-6 text-center">
            <div className="img-container h-28 mb-4">
              <img src="images/verina_cropped_04.png" alt="Specification inference from code" className="max-h-full w-auto max-w-[300px]" />
            </div>
            <h3 className="font-display text-sm font-bold mb-1.5">Specification Inference from Code</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Given existing code implementation, automatically generate formal specifications and proofs. This addresses legacy code annotation and documentation scenarios.
            </p>
          </div>
        </div>

        {/* End-to-End — full-width row so the diagram has room to breathe */}
        <div className="card p-6 md:p-8 text-center mb-4">
          <div className="img-container mb-4">
            <div className="w-full max-w-[420px] mx-auto">
              <img src="images/verina_cropped_05.png" alt="End-to-end verifiable code generation" className="w-full h-auto" />
            </div>
          </div>
          <h3 className="font-display text-sm font-bold mb-1.5">End-to-End Verifiable Code Generation</h3>
          <p className="text-xs text-gray-500 leading-relaxed max-w-xl mx-auto">
            Starting from only a natural language problem description, independently generate code, specifications, and proofs. This represents the highest level of automation in verified software development.
          </p>
        </div>

        <p className="fig-caption mb-10">
          Combinations of VERINA's foundational tasks showing real-world usage scenarios. Natural language descriptions and function signatures are omitted for brevity.
        </p>

        {/* Contextual impact chart */}
        <div className="result-panel">
          <div className="result-panel-header">
            <h3 className="font-display text-sm font-bold">Impact of Contextual Information</h3>
          </div>
          <div className="result-panel-body">
            <div className="img-container">
              <img src="images/combined_task_pass1_00.png" alt="Contextual information impact" className="max-w-xl w-full" />
            </div>
            <p className="fig-caption">Impact of contextual information on combined task performance.</p>
          </div>
        </div>
      </div>
    </section>
  )
}
