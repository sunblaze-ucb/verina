export type TakeawayAccent = 'blue' | 'amber' | 'red' | 'teal' | 'indigo' | 'green'

interface TakeawayProps {
  label?: string
  accent?: TakeawayAccent
  children: React.ReactNode
}

const ACCENT_BAR: Record<TakeawayAccent, string> = {
  blue:   'border-blue-400',
  amber:  'border-amber-400',
  red:    'border-red-400',
  teal:   'border-teal-400',
  indigo: 'border-indigo-400',
  green:  'border-green-500',
}

const ACCENT_TEXT: Record<TakeawayAccent, string> = {
  blue:   'text-blue-600',
  amber:  'text-amber-700',
  red:    'text-red-600',
  teal:   'text-teal-700',
  indigo: 'text-indigo-600',
  green:  'text-green-700',
}

export function Takeaway({ label = 'Takeaway', accent = 'blue', children }: TakeawayProps) {
  return (
    <div className={`relative my-2 mx-auto max-w-2xl pl-5 border-l-2 ${ACCENT_BAR[accent]}`}>
      <div className={`text-[10px] font-bold uppercase tracking-[0.14em] mb-1.5 ${ACCENT_TEXT[accent]}`}>
        {label}
      </div>
      <p className="text-sm text-gray-600 leading-[1.8]">{children}</p>
    </div>
  )
}
