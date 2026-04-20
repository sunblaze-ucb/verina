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
            <svg className="w-4 h-4" fill="currentColor" viewBox="0 0 24 24">
              <path d="M12 0C5.37 0 0 5.37 0 12c0 5.31 3.435 9.795 8.205 11.385.6.105.825-.255.825-.57 0-.285-.015-1.23-.015-2.235-3.015.555-3.795-.735-4.035-1.41-.135-.345-.72-1.41-1.23-1.695-.42-.225-1.02-.78-.015-.795.945-.015 1.62.87 1.845 1.23 1.08 1.815 2.805 1.305 3.495.99.105-.78.42-1.305.765-1.605-2.67-.3-5.46-1.335-5.46-5.925 0-1.305.465-2.385 1.23-3.225-.12-.3-.54-1.53.12-3.18 0 0 1.005-.315 3.3 1.23.96-.27 1.98-.405 3-.405s2.04.135 3 .405c2.295-1.56 3.3-1.23 3.3-1.23.66 1.65.24 2.88.12 3.18.765.84 1.23 1.905 1.23 3.225 0 4.605-2.805 5.625-5.475 5.925.435.375.81 1.095.81 2.22 0 1.605-.015 2.895-.015 3.3 0 .315.225.69.825.57A12.02 12.02 0 0024 12c0-6.63-5.37-12-12-12z"/>
            </svg>
            View on GitHub
          </a>
          <a href="https://huggingface.co/datasets/sunblaze-ucb/verina/" target="_blank" className="btn btn-ghost text-sm">
            Dataset on HuggingFace
          </a>
        </div>
      </div>
    </section>
  )
}
