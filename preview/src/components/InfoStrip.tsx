export function InfoStrip() {
  return (
    <section className="border-b border-gray-100 py-8 px-6">
      <div className="max-w-5xl mx-auto">
        <div className="grid grid-cols-2 md:grid-cols-5 gap-6 text-center">
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-gray-900 tabular-nums">189</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Curated Tasks</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-green-600 tabular-nums">72.6%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Best Code Score</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-amber-600 tabular-nums">52.3%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Best Spec Score</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-red-600 tabular-nums">4.9%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Proof (pass@1)</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-indigo-600 tabular-nums">20.1%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Proof (pass@64, refined)</div>
          </div>
        </div>
      </div>
    </section>
  )
}
