-- Implementation
def Compare {T : Type} [DecidableEq T] (a b : T) : Bool :=
  -- << CODE START >>
  if a = b then true else false
  -- << CODE END >>

-- Theorem: The function Compare returns true if a equals b and false if a does not equal b.
def Compare_postcond {T : Type} [DecidableEq T] (a b : T) (eq : Bool) : Prop :=
  -- << SPEC START >>
  (a = b → eq = true) ∧ (a ≠ b → eq = false)
  -- << SPEC END >>

theorem Compare_spec_satisfied {T : Type} [DecidableEq T] (a b : T) :
  Compare_postcond a b (Compare a b) := by
  -- << PROOF START >>
  sorry
  -- << PROOF END >>
