import { SectionLabel } from './SectionLabel'

export function Acknowledgements() {
  return (
    <section className="py-16 md:py-20 px-6 section-alt" id="acknowledgements">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-10">
          <SectionLabel centered>Credits</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Acknowledgements</h2>
        </div>

        <div className="grid md:grid-cols-3 gap-4">
          {/* Funding */}
          <div className="card p-5">
            <div className="text-xs font-bold text-blue-600 uppercase tracking-wider mb-2">Funding</div>
            <p className="text-xs text-gray-500 leading-relaxed mb-2">
              Based upon work supported by the{' '}
              <strong className="text-gray-700">National Science Foundation</strong> under grant no.{' '}
              <span className="tabular-nums">2229876</span>.
            </p>
            <p className="text-xs text-gray-500 leading-relaxed">
              Additional support from the National Science Foundation, the Department of Homeland
              Security, and IBM.
            </p>
            <p className="text-[11px] text-gray-400 italic leading-relaxed mt-2">
              Opinions, findings, and conclusions are those of the authors and do not necessarily
              reflect the views of the NSF or its federal agency and industry partners.
            </p>
          </div>

          {/* Community contributors */}
          <div className="card p-5">
            <div className="text-xs font-bold text-indigo-600 uppercase tracking-wider mb-2">Community</div>
            <p className="text-xs text-gray-500 leading-relaxed">
              We thank the many contributors to the VERINA dataset for bug reports, fixes, and
              quality improvements.
              {/* TODO: replace with the actual contributor list when finalized. */}
            </p>
          </div>

          {/* Berkeley course students */}
          <div className="card p-5">
            <div className="text-xs font-bold text-amber-600 uppercase tracking-wider mb-2">UC Berkeley</div>
            <p className="text-xs text-gray-500 leading-relaxed">
              We thank the students of the theorem-proving and program-verification course at UC
              Berkeley for contributing benchmark instances from LeetCode and LiveCodeBench.
            </p>
          </div>
        </div>

        <p className="text-[11px] text-gray-400 text-center italic mt-6">
          All data processing and experiments were conducted outside Meta.
        </p>
      </div>
    </section>
  )
}
