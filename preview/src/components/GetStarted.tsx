import { SiGithub, SiHuggingface } from 'react-icons/si'
import { SectionLabel } from './SectionLabel'

const INSTALL_SNIPPET = `pip install datasets
python -c "from datasets import load_dataset; ds = load_dataset('sunblaze-ucb/verina')"`

export function GetStarted() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="get-started">
      <div className="max-w-2xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Use VERINA</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Get Started</h2>
          <p className="text-sm text-gray-500 max-w-md mx-auto mt-3 leading-relaxed">
            VERINA is open-source and ready to use. Evaluate your model in three steps.
          </p>
        </div>

        <div className="space-y-4">
          <div className="flex gap-4 items-start">
            <div className="step-number mt-0.5">1</div>
            <div className="flex-1 min-w-0">
              <h3 className="font-display text-sm font-bold mb-0.5">Download the dataset</h3>
              <div className="code-block mt-2">
                <pre><code className="language-bash text-xs">{INSTALL_SNIPPET}</code></pre>
              </div>
            </div>
          </div>

          <div className="flex gap-4 items-start">
            <div className="step-number mt-0.5">2</div>
            <div>
              <h3 className="font-display text-sm font-bold mb-0.5">Run your model</h3>
              <p className="text-xs text-gray-500 leading-relaxed">
                Generate code, specifications, or proofs using your model of choice. See our{' '}
                <a href="https://github.com/sunblaze-ucb/verina/" target="_blank" className="text-blue-600 hover:underline">evaluation code</a>
                {' '}for prompting templates and pipeline setup.
              </p>
            </div>
          </div>

          <div className="flex gap-4 items-start">
            <div className="step-number mt-0.5">3</div>
            <div>
              <h3 className="font-display text-sm font-bold mb-0.5">Evaluate with Lean</h3>
              <p className="text-xs text-gray-500 leading-relaxed">
                Run generated outputs against our test suites and Lean type-checker. Specification metrics are computed automatically via our evaluation framework.
              </p>
            </div>
          </div>
        </div>

        <div className="flex items-center justify-center gap-3 mt-10">
          <a href="https://github.com/sunblaze-ucb/verina/" target="_blank" className="btn btn-ghost text-sm">
            <SiGithub className="w-4 h-4" aria-hidden="true" />
            View on GitHub
          </a>
          <a href="https://huggingface.co/datasets/sunblaze-ucb/verina/" target="_blank" className="btn btn-ghost text-sm">
            <SiHuggingface className="w-4 h-4" aria-hidden="true" />
            Dataset on HuggingFace
          </a>
        </div>
      </div>
    </section>
  )
}
