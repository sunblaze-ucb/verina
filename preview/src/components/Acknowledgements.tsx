export function Acknowledgements() {
  return (
    <section className="py-12 px-6 section-alt" id="acknowledgements">
      <div className="max-w-2xl mx-auto reveal text-center">
        <h3 className="font-display text-lg font-bold mb-3">Acknowledgements</h3>
        <p className="text-xs text-gray-500 leading-relaxed mb-3">
          We thank the following individuals for contributions to the VERINA dataset, including bug reports, fixes, and quality improvements:
        </p>
        <p className="text-xs text-gray-600 font-medium">
          {/* PLACEHOLDER: Add names of contributors here */}
          Contributor Name 1, Contributor Name 2, Contributor Name 3, Contributor Name 4
        </p>
        <p className="text-xs text-gray-400 mt-3">
          We also thank the students of the theorem proving and program verification course at UC Berkeley for their contributions to benchmark instances.
        </p>
      </div>
    </section>
  )
}
