import { SectionLabel } from './SectionLabel'

export function Features() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="features">
      <div className="max-w-4xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Benchmark</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Why VERINA?</h2>
        </div>

        {/* Two-up rationale: why VCG matters, why VERINA matters */}
        <div className="grid md:grid-cols-2 gap-4 mb-10">
          <div className="relative rounded-[10px] border border-gray-200 bg-white p-6">
            <div className="text-[10px] font-bold text-gray-400 uppercase tracking-[0.14em] mb-2">
              Why verifiable code generation?
            </div>
            <p className="text-sm md:text-[15px] text-gray-600 leading-[1.75]">
              <strong className="text-gray-800">Verifiable code generation</strong> offers higher levels of correctness assurance and automation in software development, potentially addressing the productivity bottleneck caused by bugs and security vulnerabilities in LLM-generated code.
            </p>
          </div>

          <div className="relative rounded-[10px] border border-blue-200 bg-blue-50/60 p-6 border-l-[3px] border-l-blue-500">
            <div className="text-[10px] font-bold text-blue-600 uppercase tracking-[0.14em] mb-2">
              Why VERINA?
            </div>
            <p className="text-sm md:text-[15px] text-gray-700 leading-[1.75]">
              <strong className="text-gray-900">VERINA establishes a foundation for advancing verifiable code generation research</strong>, providing rigorous evaluation capabilities and clear directions toward more reliable, formally verified automated programming systems.
            </p>
          </div>
        </div>

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

        <p className="text-xs text-gray-500 leading-relaxed text-center max-w-2xl mx-auto mt-8 italic">
          Our findings underscore the critical need for improving LLM-based theorem proving capabilities in verification domains.
        </p>
      </div>
    </section>
  )
}
