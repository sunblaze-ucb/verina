import { SiGithub, SiHuggingface } from 'react-icons/si'
import { SectionLabel } from './SectionLabel'

export function GetStarted() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="get-started">
      <div className="max-w-2xl mx-auto reveal text-center">
        <SectionLabel centered>Use VERINA</SectionLabel>
        <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Get Started</h2>
        <p className="text-sm text-gray-500 max-w-md mx-auto mt-3 leading-relaxed">
          VERINA is open-source. Head to the GitHub repo for setup and evaluation instructions.
        </p>

        <div className="flex items-center justify-center gap-3 mt-7 flex-wrap">
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
