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
      </div>
    </section>
  )
}
