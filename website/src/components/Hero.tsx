import { SiGithub, SiHuggingface } from 'react-icons/si'

export function Hero() {
  return (
    <section className="hero-gradient flex flex-col items-center justify-center text-white px-6 pt-24 pb-16 md:pt-28 md:pb-20">
      <div className="relative z-10 max-w-3xl mx-auto text-center">
        <span className="badge bg-white/10 text-blue-200 border border-white/15 mb-5">ICLR 2026</span>

        <h1 className="font-display text-[1.625rem] sm:text-3xl md:text-4xl font-extrabold leading-[1.15] tracking-tight mt-2 text-balance break-words">
          VERINA: Benchmarking Verifiable Code Generation
        </h1>

        {/* Authors */}
        <div className="mt-7 text-[15px] md:text-base font-semibold text-blue-100/90 leading-relaxed">
          <a href="https://zhe.sh/" target="_blank" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Zhe Ye</a><sup>1</sup>,{' '}
          <a href="#" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Zhengxu Yan</a><sup>1</sup>,{' '}
          <a href="https://jxhe.info/" target="_blank" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Jingxuan He</a><sup>1</sup>,{' '}
          <a href="#" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Timothe Kasriel</a><sup>1</sup>,{' '}
          <a href="https://yangky11.github.io/" target="_blank" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Kaiyu Yang</a><sup>2</sup>,{' '}
          <a href="https://dawnsong.io/" target="_blank" className="underline underline-offset-4 decoration-blue-300/40 hover:text-white hover:decoration-white transition-colors">Dawn Song</a><sup>1</sup>
          <div className="mt-2 text-xs text-blue-300/60">
            <sup>1</sup>UC Berkeley &nbsp;·&nbsp; <sup>2</sup>Meta FAIR
          </div>
        </div>

        {/* Buttons */}
        <div className="flex flex-wrap items-center justify-center gap-2.5 mt-7">
          <a href="https://arxiv.org/pdf/2505.23135.pdf" target="_blank" className="btn btn-primary">
            <i className="ai ai-arxiv text-base"></i> Paper
          </a>
          <a href="https://github.com/sunblaze-ucb/verina/" target="_blank" className="btn btn-outline">
            <SiGithub className="w-4 h-4" aria-hidden="true" />
            Code
          </a>
          <a href="https://huggingface.co/datasets/sunblaze-ucb/verina/" target="_blank" className="btn btn-outline">
            <SiHuggingface className="w-4 h-4" aria-hidden="true" />
            Dataset
          </a>
        </div>
      </div>
    </section>
  )
}
