import { cn } from '@/lib/utils'

interface SectionLabelProps {
  children: React.ReactNode
  centered?: boolean
  className?: string
}

export function SectionLabel({ children, centered = false, className }: SectionLabelProps) {
  return (
    <div className={cn('section-label', centered && 'justify-center', className)}>
      {children}
    </div>
  )
}
