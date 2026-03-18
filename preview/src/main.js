import './style.css'

document.addEventListener('DOMContentLoaded', () => {
  // Highlight.js
  if (window.hljs) {
    hljs.highlightAll()
  }

  // Sticky nav background on scroll
  const nav = document.getElementById('nav')
  if (nav) {
    const onScroll = () => {
      nav.classList.toggle('scrolled', window.scrollY > 40)
    }
    window.addEventListener('scroll', onScroll, { passive: true })
    onScroll()
  }

  // Scroll reveal
  const reveals = document.querySelectorAll('.reveal')
  const observer = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          entry.target.classList.add('visible')
        }
      })
    },
    { threshold: 0.08, rootMargin: '0px 0px -40px 0px' }
  )
  reveals.forEach((el) => observer.observe(el))
})

// Copy BibTeX
window.copyBibtex = function () {
  const code = document.getElementById('bibtex-code')
  navigator.clipboard.writeText(code.textContent).then(() => {
    const btn = document.querySelector('.copy-btn')
    const original = btn.textContent
    btn.textContent = 'Copied!'
    setTimeout(() => { btn.textContent = original }, 2000)
  })
}
