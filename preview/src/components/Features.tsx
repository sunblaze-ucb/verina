import { SectionLabel } from './SectionLabel'

export function Features() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="features">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Benchmark</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Why VERINA?</h2>
        </div>

        {/* Why VCG? — plain prose, no card chrome */}
        <p className="text-sm md:text-[15px] text-gray-600 leading-[1.85] text-center max-w-2xl mx-auto mb-10">
          <strong className="text-gray-800">Verifiable code generation</strong> offers higher levels of correctness assurance and automation in software development, potentially addressing the productivity bottleneck caused by bugs and security vulnerabilities in LLM-generated code.
        </p>

        <div className="grid sm:grid-cols-2 gap-4">
          <div className="card p-5">
            <div className="text-xs font-bold text-blue-600 uppercase tracking-wider mb-1.5">189 Tasks</div>
            <h3 className="font-display text-sm font-bold mb-1">Comprehensive Coverage</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Manually curated with varying difficulty: VERINA-A (108, translated from Dafny) and VERINA-B (81, student-written and harder). Each task includes descriptions, code, specifications, and test suites.
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

        {/* Why VERINA? — thesis callout, distinct from the benefit cards */}
        <div className="insight-box mt-10 max-w-3xl mx-auto text-sm md:text-[15px] text-gray-700 leading-[1.8]">
          <p>
            <strong className="text-gray-900">VERINA establishes a foundation for advancing verifiable code generation research</strong>, providing both rigorous evaluation capabilities and clear directions toward more reliable and formally verified automated programming systems. Our findings underscore the critical need for improving LLM-based theorem proving capabilities in verification domains.
          </p>
        </div>
      </div>
    </section>
  )
}
