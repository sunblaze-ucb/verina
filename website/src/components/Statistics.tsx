import { SectionLabel } from './SectionLabel'

export function Statistics() {
  return (
    <section className="py-16 md:py-20 px-6" id="statistics">
      <div className="max-w-2xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Data</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Benchmark Statistics</h2>
        </div>

        <table className="data-table">
          <thead>
            <tr>
              <th>Metric</th>
              <th>Median</th>
              <th>Max</th>
            </tr>
          </thead>
          <tbody>
            <tr><td>Words in Description</td><td>110</td><td>296</td></tr>
            <tr><td>Lines of Code (Implementation)</td><td>9</td><td>38</td></tr>
            <tr><td>Lines of Code (Specification)</td><td>4</td><td>62</td></tr>
            <tr><td>Positive Test Cases</td><td>5</td><td>13</td></tr>
            <tr><td>Negative Test Cases</td><td>12</td><td>27</td></tr>
          </tbody>
        </table>
      </div>
    </section>
  )
}
