export function Acknowledgements() {
  return (
    <section className="py-12 px-6 section-alt" id="acknowledgements">
      <div className="max-w-2xl mx-auto reveal text-center">
        <h3 className="font-display text-lg font-bold mb-3">Acknowledgements</h3>
        <p className="text-xs text-gray-500 leading-relaxed mb-3">
          We thank the many contributors to the VERINA dataset for bug reports, fixes, and quality improvements.
          {/* TODO: replace with the actual contributor list when finalized. */}
        </p>
        <p className="text-xs text-gray-400">
          We also thank the students of the theorem-proving and program-verification course at UC Berkeley for their contributions to benchmark instances.
        </p>
      </div>
    </section>
  )
}
