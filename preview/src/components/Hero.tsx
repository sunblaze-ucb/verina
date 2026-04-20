export function Hero() {
  return (
    <section className="hero-gradient flex flex-col items-center justify-center text-white px-6 pt-24 pb-16 md:pt-28 md:pb-20">
      <div className="relative z-10 max-w-3xl mx-auto text-center">
        <span className="badge bg-white/10 text-blue-200 border border-white/15 mb-5">ICLR 2026</span>

        <h1 className="font-display text-4xl md:text-5xl font-extrabold leading-[1.1] tracking-tight mt-2">
          VERINA
        </h1>
        <p className="text-lg md:text-xl text-blue-100/90 mt-2 tracking-tight font-medium">
          Benchmarking Verifiable Code Generation
        </p>

        <p className="text-sm text-blue-200/70 mt-5 max-w-lg mx-auto leading-relaxed">
          189 manually curated tasks in Lean for evaluating code, specification, and proof generation—and their compositions.
        </p>

        {/* Authors */}
        <div className="mt-6 text-[13px] text-blue-200/80 leading-relaxed">
          <a href="https://zhe.sh/" target="_blank" className="hover:text-white transition-colors">Zhe Ye</a><sup>1</sup>,{' '}
          <a href="#" className="hover:text-white transition-colors">Zhengxu Yan</a><sup>1</sup>,{' '}
          <a href="https://jxhe.info/" target="_blank" className="hover:text-white transition-colors">Jingxuan He</a><sup>1</sup>,{' '}
          <a href="#" className="hover:text-white transition-colors">Timothe Kasriel</a><sup>1</sup>,{' '}
          <a href="https://yangky11.github.io/" target="_blank" className="hover:text-white transition-colors">Kaiyu Yang</a><sup>2*</sup>,{' '}
          <a href="https://dawnsong.io/" target="_blank" className="hover:text-white transition-colors">Dawn Song</a><sup>1</sup>
          <div className="mt-1 text-xs text-blue-300/60">
            <sup>1</sup>UC Berkeley &nbsp;·&nbsp; <sup>2</sup>Meta FAIR
          </div>
        </div>

        {/* Buttons */}
        <div className="flex flex-wrap items-center justify-center gap-2.5 mt-7">
          <a href="https://arxiv.org/pdf/2505.23135.pdf" target="_blank" className="btn btn-primary">
            <i className="ai ai-arxiv text-base"></i> Paper
          </a>
          <a href="https://github.com/sunblaze-ucb/verina/" target="_blank" className="btn btn-outline">
            <svg className="w-4 h-4" fill="currentColor" viewBox="0 0 24 24">
              <path d="M12 0C5.37 0 0 5.37 0 12c0 5.31 3.435 9.795 8.205 11.385.6.105.825-.255.825-.57 0-.285-.015-1.23-.015-2.235-3.015.555-3.795-.735-4.035-1.41-.135-.345-.72-1.41-1.23-1.695-.42-.225-1.02-.78-.015-.795.945-.015 1.62.87 1.845 1.23 1.08 1.815 2.805 1.305 3.495.99.105-.78.42-1.305.765-1.605-2.67-.3-5.46-1.335-5.46-5.925 0-1.305.465-2.385 1.23-3.225-.12-.3-.54-1.53.12-3.18 0 0 1.005-.315 3.3 1.23.96-.27 1.98-.405 3-.405s2.04.135 3 .405c2.295-1.56 3.3-1.23 3.3-1.23.66 1.65.24 2.88.12 3.18.765.84 1.23 1.905 1.23 3.225 0 4.605-2.805 5.625-5.475 5.925.435.375.81 1.095.81 2.22 0 1.605-.015 2.895-.015 3.3 0 .315.225.69.825.57A12.02 12.02 0 0024 12c0-6.63-5.37-12-12-12z"/>
            </svg>
            Code
          </a>
          <a href="https://huggingface.co/datasets/sunblaze-ucb/verina/" target="_blank" className="btn btn-outline">
            <svg className="w-4 h-4" viewBox="0 0 16 16" fill="currentColor">
              <path fillRule="evenodd" clipRule="evenodd" d="M15.02 12.91c.13-.3.14-.64.04-.95.11-.27.12-.57.05-.85a1.5 1.5 0 00-.18-.4c.13-.46 0-.95-.32-1.3a1.4 1.4 0 00-.44-.31c.1-.45.15-.92.15-1.39C14.32 4.19 11.48 1.33 7.96 1.33S1.6 4.19 1.6 7.71c0 .49.06.97.16 1.42a1.4 1.4 0 00-.37.28c-.28.31-.4.7-.34 1.12l.07.18a1.5 1.5 0 00-.18.4c-.07.28-.05.58.05.85a1.1 1.1 0 00.04.95c.24.54.79.88 1.55 1.18.85.34 1.78.58 2.74.58.77 0 1.44-.19 1.93-.62.25.03.51.05.77.05.28 0 .56-.02.83-.05.49.44 1.16.63 1.94.63.96 0 1.89-.24 2.73-.58.76-.3 1.32-.64 1.55-1.18z"/>
            </svg>
            Dataset
          </a>
        </div>
      </div>
    </section>
  )
}
