-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def trapLoop (height : List Nat) (left right leftMax rightMax water : Nat) : Nat :=
  if h : left < right then
    let hLeft := height[left]!
    let hRight := height[right]!
    if hLeft < hRight then
      let (leftMax, water) :=
        if hLeft >= leftMax then (hLeft, water) else (leftMax, water + (leftMax - hLeft))
      trapLoop height (left + 1) right leftMax rightMax water
    else
      let (rightMax, water) :=
        if hRight >= rightMax then (hRight, water) else (rightMax, water + (rightMax - hRight))
      trapLoop height left (right - 1) leftMax rightMax water
  else
    water
termination_by right - left
-- !benchmark @end code_aux


def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  -- !benchmark @start code
  trapLoop height 0 (height.length - 1) 0 0 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  -- !benchmark @start postcond
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem trapRainWater_spec_satisfied (height: List Nat) (h_precond : trapRainWater_precond (height)) :
    trapRainWater_postcond (height) (trapRainWater (height) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
