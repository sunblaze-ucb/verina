import { useState } from 'react'
import { MODELS, type ModelResult } from '@/lib/results'

type SortKey = 'name' | 'code' | 'spec' | 'proof' | 'codeA' | 'codeB' | 'codeSpec' | 'e2e'

function cmp<T extends string | number | undefined>(a: T, b: T): number {
  if (a === undefined && b === undefined) return 0
  if (a === undefined) return 1
  if (b === undefined) return -1
  if (typeof a === 'number' && typeof b === 'number') return b - a
  return String(a).localeCompare(String(b))
}

const COLS: Array<{ key: SortKey; label: string; align: 'left' | 'right' }> = [
  { key: 'name',     label: 'Model',        align: 'left' },
  { key: 'code',     label: 'Code',         align: 'right' },
  { key: 'spec',     label: 'Spec S&C',     align: 'right' },
  { key: 'proof',    label: 'Proof',        align: 'right' },
  { key: 'codeA',    label: 'Code-A',       align: 'right' },
  { key: 'codeB',    label: 'Code-B',       align: 'right' },
  { key: 'codeSpec', label: 'Code & Spec',  align: 'right' },
  { key: 'e2e',      label: 'E2E',          align: 'right' },
]

const FORMAT = (v: number | undefined) => (v === undefined ? '—' : v.toFixed(1))

export function Leaderboard() {
  const [sortKey, setSortKey] = useState<SortKey>('code')
  const sorted = [...MODELS].sort((a, b) => cmp(a[sortKey], b[sortKey]))

  return (
    <div className="result-panel">
      <div className="result-panel-header">
        <h3 className="font-display text-sm font-bold">Full Leaderboard (pass@1)</h3>
      </div>
      <div className="result-panel-body">
        <p className="text-xs text-gray-500 mb-3 leading-relaxed">
          Click a column header to sort. Code-A / Code-B are CodeGen pass@1 on the VERINA-A and VERINA-B splits. Source: paper Tables 8–10 and Figures 5–6.
        </p>
        <div className="overflow-x-auto">
          <table className="data-table text-[13px]">
            <thead>
              <tr>
                {COLS.map(({ key, label, align }) => (
                  <th
                    key={key}
                    scope="col"
                    onClick={() => setSortKey(key)}
                    className={`cursor-pointer hover:text-blue-600 select-none transition-colors ${align === 'right' ? 'text-right' : ''} ${sortKey === key ? 'text-blue-600' : ''}`}
                  >
                    {label}
                    {sortKey === key && <span className="ml-1">▾</span>}
                  </th>
                ))}
              </tr>
            </thead>
            <tbody>
              {sorted.map((m: ModelResult) => (
                <tr key={m.name}>
                  <td>{m.short ?? m.name}</td>
                  <td className="text-right">{FORMAT(m.code)}</td>
                  <td className="text-right">{FORMAT(m.spec)}</td>
                  <td className="text-right">{FORMAT(m.proof)}</td>
                  <td className="text-right">{FORMAT(m.codeA)}</td>
                  <td className="text-right">{FORMAT(m.codeB)}</td>
                  <td className="text-right">{FORMAT(m.codeSpec)}</td>
                  <td className="text-right">{FORMAT(m.e2e)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </div>
  )
}
