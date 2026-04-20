import { useScrollReveal } from '@/hooks/useScrollReveal'
import { Nav } from '@/components/Nav'
import { Hero } from '@/components/Hero'
import { InfoStrip } from '@/components/InfoStrip'
import { Abstract } from '@/components/Abstract'
import { Overview } from '@/components/Overview'
import { Features } from '@/components/Features'
import { DataFormat } from '@/components/DataFormat'
import { SpecEval } from '@/components/SpecEval'
import { Statistics } from '@/components/Statistics'
import { Results } from '@/components/Results'
import { Combinations } from '@/components/Combinations'
import { GetStarted } from '@/components/GetStarted'
import { Citation } from '@/components/Citation'
import { Acknowledgements } from '@/components/Acknowledgements'
import { Footer } from '@/components/Footer'

export default function App() {
  useScrollReveal()
  return (
    <>
      <Nav />
      <Hero />
      <InfoStrip />
      <Abstract />
      <Overview />
      <Features />
      <DataFormat />
      <SpecEval />
      <Statistics />
      <Results />
      <Combinations />
      <GetStarted />
      <Citation />
      <Acknowledgements />
      <Footer />
    </>
  )
}
