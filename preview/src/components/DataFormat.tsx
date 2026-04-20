import { SectionLabel } from './SectionLabel'
import { CodeBlock } from './CodeBlock'

const LEAN_EXAMPLE = `-- Description: Remove an element from an array at a specified index...

-- Code implementation
def removeElement (s : Array Int) (k : Nat)
    (h_precond : removeElement_pre s k) : Array Int :=
  s.eraseIdx! k

-- Pre-condition
def removeElement_pre (s : Array Int) (k : Nat) : Prop :=
  k < s.size

-- Post-condition
def removeElement_post (s : Array Int) (k : Nat) (result: Array Int)
    (h_precond : removeElement_pre s k) : Prop :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

-- Proof (establishing code-specification alignment)
theorem removeElement_spec (s: Array Int) (k: Nat)
    (h_precond : removeElement_pre s k) :
    removeElement_post s k (removeElement s k h_precond) h_precond := by
  unfold removeElement removeElement_post
  simp_all [Array.eraseIdx!] ...

-- Test cases
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[1, 2, 4, 5])  -- Positive
(s : #[1, 2, 3, 4, 5]) (k : 5)                             -- Negative: violates pre-condition
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[1, 2, 4])       -- Negative: violates post-condition`

export function DataFormat() {
  return (
    <section className="py-16 md:py-20 px-6" id="data-format">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Format</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Task Structure</h2>
          <p className="text-sm text-gray-500 max-w-md mx-auto mt-3 leading-relaxed">
            Each VERINA instance includes a description, code, specifications, proofs, and comprehensive test cases—all in Lean.
          </p>
        </div>

        <CodeBlock language="lean" title="example.lean" code={LEAN_EXAMPLE} />
      </div>
    </section>
  )
}
