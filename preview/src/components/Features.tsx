import { SectionLabel } from './SectionLabel'

export function Features() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="features">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Benchmark</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Why VERINA?</h2>
        </div>

        <div className="grid sm:grid-cols-2 gap-4">
          <div className="card p-5">
            <div className="text-xs font-bold text-blue-600 uppercase tracking-wider mb-1.5">189 Tasks</div>
            <h3 className="font-display text-sm font-bold mb-1">Comprehensive Coverage</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Manually curated with varying difficulty: VERINA-BASIC (108) and VERINA-ADV (81). Each task includes descriptions, code, specifications, and test suites.
            </p>
          </div>

          <div className="card p-5">
            <div className="text-xs font-bold text-indigo-600 uppercase tracking-wider mb-1.5">Composable</div>
            <h3 className="font-display text-sm font-bold mb-1">Modular Design</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Evaluate individual tasks or their flexible combinations—from specification-guided coding to end-to-end verified generation.
            </p>
          </div>

          <div className="card p-5">
            <div className="text-xs font-bold text-green-600 uppercase tracking-wider mb-1.5">100% Coverage</div>
            <h3 className="font-display text-sm font-bold mb-1">High-Quality Test Suites</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Full line coverage with both positive and negative test cases, ensuring robust and reliable evaluation.
            </p>
          </div>

          <div className="card p-5">
            <div className="text-xs font-bold text-amber-600 uppercase tracking-wider mb-1.5">Automated</div>
            <h3 className="font-display text-sm font-bold mb-1">Novel Spec Metrics</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              A testing-based framework that automatically measures soundness and completeness of generated specifications.
            </p>
          </div>
        </div>
      </div>
    </section>
  )
}
