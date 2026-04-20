import { SectionLabel } from './SectionLabel'

export function Abstract() {
  return (
    <>
      <section className="py-16 md:py-20 px-6" id="abstract">
        <div className="max-w-2xl mx-auto reveal">
          <SectionLabel>Abstract</SectionLabel>
          <div className="text-[15px] md:text-base leading-[1.8] text-gray-600">
            <p>
              Large language models (LLMs) are increasingly integrated in software development, but ensuring correctness in LLM-generated code remains challenging. <strong className="text-gray-800">Verifiable code generation</strong>—jointly generating code, specifications, and proofs of code-specification alignment—offers a promising path forward. We introduce <strong className="text-gray-800">VERINA</strong>, a high-quality benchmark enabling comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions. VERINA consists of <strong className="text-gray-800">189 manually curated coding tasks</strong> in Lean with detailed problem descriptions, reference implementations, formal specifications, and extensive test suites. The best model, OpenAI o3, achieves <strong className="text-gray-800">72.6% code correctness, 52.3% specification soundness &amp; completeness, and only 4.9% proof success</strong>—revealing that proof generation remains a critical bottleneck.
            </p>
          </div>
        </div>
      </section>
      <div className="section-divider"></div>
    </>
  )
}
