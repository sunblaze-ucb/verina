export function InfoStrip() {
  return (
    <section className="border-b border-gray-100 py-8 px-6">
      <div className="max-w-4xl mx-auto">
        <div className="grid grid-cols-2 md:grid-cols-4 gap-6 text-center">
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-gray-900">189</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Curated Tasks</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-green-600">72.6%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Best Code Score</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-amber-600">52.3%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Best Spec Score</div>
          </div>
          <div>
            <div className="font-display text-2xl font-extrabold tracking-tight text-red-600">4.9%</div>
            <div className="text-xs text-gray-500 font-medium mt-0.5 uppercase tracking-wider">Best Proof Score</div>
          </div>
        </div>
      </div>
    </section>
  )
}
