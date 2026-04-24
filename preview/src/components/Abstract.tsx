import { SectionLabel } from './SectionLabel'

export function Abstract() {
  return (
    <>
      <section className="py-16 md:py-20 px-6" id="abstract">
        <div className="max-w-3xl mx-auto reveal">
          <SectionLabel>Abstract</SectionLabel>
          <div className="text-[15px] md:text-base leading-[1.8] text-gray-600 text-justify hyphens-auto [text-align-last:left]">
            <p>
              Large language models (LLMs) are increasingly integrated in software development, but ensuring correctness in LLM-generated code remains challenging and often requires costly manual review. <strong className="text-gray-800">Verifiable code generation</strong>—jointly generating code, specifications, and proofs of code-specification alignment—offers a promising path to address this limitation and further unleash LLMs' benefits in coding. Yet, there exists a significant gap in evaluation: current benchmarks often lack support for end-to-end verifiable code generation. In this paper, we introduce <strong className="text-gray-800">VERINA</strong> (Verifiable Code Generation Arena), a high-quality benchmark enabling a comprehensive and modular evaluation of code, specification, and proof generation as well as their compositions. VERINA consists of <strong className="text-gray-800">189 manually curated coding tasks</strong> in Lean, with detailed problem descriptions, reference implementations, formal specifications, and extensive test suites. Our extensive evaluation of state-of-the-art LLMs reveals significant challenges in verifiable code generation, especially in proof generation, underscoring the need for improving LLM-based theorem provers in verification domains. The best model, OpenAI o3, achieves a <strong className="text-gray-800">72.6% code correctness rate, 52.3% for specification soundness and completeness, and a mere 4.9% proof success rate</strong> (based on one trial per task). We hope VERINA will catalyze progress in verifiable code generation by providing a rigorous and comprehensive benchmark.
            </p>
          </div>
        </div>
      </section>
      <div className="section-divider"></div>
    </>
  )
}
