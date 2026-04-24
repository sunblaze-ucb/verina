import { SectionLabel } from './SectionLabel'

export function Overview() {
  return (
    <section className="py-16 md:py-20 px-6" id="overview">
      <div className="max-w-5xl mx-auto reveal">
        <div className="text-center mb-12">
          <SectionLabel centered>Overview</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Three Foundational Tasks</h2>
          <p className="text-sm text-gray-500 max-w-lg mx-auto mt-3 leading-relaxed">
            <b>Verifiable code generation</b> requires models to jointly produce code, formal specifications, and machine-checkable proofs.
          </p>
        </div>

        <div className="grid md:grid-cols-3 gap-5">
          <div className="card p-5 flex flex-col items-center text-center">
            <div className="img-container h-24 mb-4">
              <img src="images/verina_cropped_00.png" alt="Code Generation" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-sm font-bold mb-1.5">Code Implementation</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Functional code that solves the programming problem. Given a natural language description and function signature, models generate executable code implementations. Model can optionally use existing specification as context.
            </p>
          </div>

          <div className="card p-5 flex flex-col items-center text-center">
            <div className="img-container h-24 mb-4">
              <img src="images/verina_cropped_01.png" alt="Specification Generation" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-sm font-bold mb-1.5">Formal Specifications</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Pre-conditions and post-conditions that formally describe expected behavior. Models can optionally use existing code as context.
            </p>
          </div>

          <div className="card p-5 flex flex-col items-center text-center">
            <div className="img-container h-24 mb-4">
              <img src="images/verina_cropped_02.png" alt="Proof Generation" className="max-h-full w-auto max-w-[160px]" />
            </div>
            <h3 className="font-display text-sm font-bold mb-1.5">Formal Proofs</h3>
            <p className="text-xs text-gray-500 leading-relaxed">
              Machine-checkable proofs that verify code-specification alignment. Given code and specifications, models construct logical arguments for correctness.
            </p>
          </div>
        </div>

        <p className="fig-caption mt-3">
          VERINA's three foundational tasks. Dashed arrows represent optional inputs.
        </p>

        <p className="text-sm md:text-base text-gray-600 leading-[1.8] text-center max-w-3xl mx-auto mt-10">
          This approach offers higher levels of correctness assurance and automation in software development, potentially addressing the productivity bottleneck caused by bugs and security vulnerabilities in LLM-generated code.
        </p>

        <div className="insight-box mt-6 max-w-3xl mx-auto text-sm md:text-base text-gray-600 leading-[1.8]">
          <p>
            <strong className="text-gray-800">VERINA establishes a foundation for advancing verifiable code generation research</strong>, providing both rigorous evaluation capabilities and clear directions toward more reliable and formally verified automated programming systems. Our findings underscore the critical need for improving LLM-based theorem proving capabilities in verification domains.
          </p>
        </div>
      </div>
    </section>
  )
}
