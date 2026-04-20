import { cn } from '@/lib/utils'
import { useStickyNav } from '@/hooks/useStickyNav'

export function Nav() {
  const scrolled = useStickyNav()
  return (
    <nav className={cn('nav', scrolled && 'scrolled')}>
      <div className="max-w-6xl mx-auto px-6 h-14 flex items-center justify-between">
        <a href="#" className="nav-logo">VERINA</a>
        <div className="hidden md:flex items-center gap-6">
          <a href="#overview" className="nav-link">Overview</a>
          <a href="#results" className="nav-link">Results</a>
          <a href="#get-started" className="nav-link">Get Started</a>
          <a href="#citation" className="nav-link">Cite</a>
        </div>
      </div>
    </nav>
  )
}
