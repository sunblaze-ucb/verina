import { SectionLabel } from './SectionLabel'

export function Acknowledgements() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="acknowledgements">
      <div className="max-w-2xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Credits</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Acknowledgements</h2>
        </div>

        {/* Community — primary */}
        <div className="insight-box mb-6">
          <div className="text-xs font-bold text-blue-600 uppercase tracking-wider mb-2">Community contributors</div>
          <p className="text-sm text-gray-600 leading-relaxed mb-3">
            VERINA is a living benchmark. We're grateful to everyone in the community who has improved
            its quality — <strong className="text-gray-800">reporting bugs</strong>,{' '}
            <strong className="text-gray-800">fixing errors</strong> in specifications and tests,{' '}
            <strong className="text-gray-800">validating instances</strong>, and suggesting
            clarifications. Every accepted fix strengthens the benchmark.
          </p>
          <p className="text-xs text-gray-500 leading-relaxed">
            {/* TODO: insert a curated contributor list here when finalized. */}
            See the{' '}
            <a
              href="https://github.com/sunblaze-ucb/verina/graphs/contributors"
              target="_blank"
              className="text-blue-600 hover:underline"
            >
              GitHub contributors page
            </a>{' '}
            for the full list.
          </p>
        </div>

        {/* UC Berkeley course — secondary */}
        <p className="text-xs text-gray-500 leading-relaxed text-center mb-8">
          We also thank the students of the theorem-proving and program-verification course at
          UC Berkeley for contributing benchmark instances from LeetCode and LiveCodeBench.
        </p>

        {/* Funding + Meta note — small footer */}
        <div className="text-center text-[11px] text-gray-400 leading-relaxed space-y-1 border-t border-gray-200/60 pt-5">
          <p>
            Based upon work supported by the{' '}
            <strong className="text-gray-500">National Science Foundation</strong> (grant no.{' '}
            <span className="tabular-nums">2229876</span>), with partner support from the NSF,
            the Department of Homeland Security, and IBM.
          </p>
          <p className="italic">
            All data processing and experiments were conducted outside Meta.
          </p>
        </div>
      </div>
    </section>
  )
}
