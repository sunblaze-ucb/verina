import { SectionLabel } from './SectionLabel'
import { CodeBlock } from './CodeBlock'

const LEAN_EXAMPLE = `-- Natural language description of the coding problem
-- Remove an element from a given array of integers at a specified index...

-- Pre-condition
def removeElement_pre (s : Array Int) (k : Nat) : Prop :=
  k < s.size

-- Code implementation
def removeElement (s : Array Int) (k : Nat)
    (h_precond : removeElement_pre s k) : Array Int :=
  s.eraseIdx! k

-- Post-condition
def removeElement_post (s : Array Int) (k : Nat) (result: Array Int)
    (h_precond : removeElement_pre s k) : Prop :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

-- Formal Proof (establishing code-specification alignment)
theorem removeElement_spec (s: Array Int) (k: Nat)
    (h_precond : removeElement_pre s k) :
    removeElement_post s k (removeElement s k h_precond) h_precond := by
  unfold removeElement removeElement_postcond
  unfold removeElement_precond at h_precond
  simp_all
  unfold Array.eraseIdx!
  simp [h_precond]
  constructor
  · intro i hi
    have hi' : i < s.size - 1 := by
      have hk := Nat.le_sub_one_of_lt h_precond
      exact Nat.lt_of_lt_of_le hi hk
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
    unfold Array.getD
    simp [hi', Nat.lt_trans hi h_precond, Array.getElem_eraseIdx, hi]
  · intro i hi hi'
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
    unfold Array.getD
    have hi'' : i + 1 < s.size := by exact Nat.add_lt_of_lt_sub hi
    simp [hi, hi'']
    have : ¬ i < k := by simp [hi']
    simp [Array.getElem_eraseIdx, this]

-- Comprehensive test cases (both positive and negative)
-- Positive test with valid inputs and output
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[1, 2, 4, 5])
-- Negative test: inputs violate the pre-condition
(s : #[1, 2, 3, 4, 5]) (k : 5)
-- Negative test: output violates the first clause of the post-condition
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[1, 2, 4])
-- Negative test: output violates the second clause of the post-condition
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[2, 2, 4, 5])
-- Negative test: output violates the third clause of the post-condition
(s : #[1, 2, 3, 4, 5]) (k : 2) (result : #[1, 2, 4, 4])`

export function DataFormat() {
  return (
    <section className="py-16 md:py-20 px-6" id="data-format">
      <div className="max-w-3xl mx-auto reveal">
        <div className="text-center mb-8">
          <SectionLabel centered>Format</SectionLabel>
          <h2 className="font-display text-2xl md:text-3xl font-bold mt-1">Task Structure</h2>
          <p className="text-sm text-gray-500 max-w-md mx-auto mt-3 leading-relaxed">
            Each VERINA instance includes a description, code, specifications, (optionally) proofs, and comprehensive test cases—all in Lean.
          </p>
        </div>

        <CodeBlock language="lean" title="example.lean" code={LEAN_EXAMPLE} />
      </div>
    </section>
  )
}
