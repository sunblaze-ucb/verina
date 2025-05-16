-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  -- !benchmark @start code
  -- Creates list of (index, value) pairs
  let indexed := a.toList.zipIdx

  -- Find the first pair where the value is odd
  let found := List.find? (fun (x, _) => isOdd x) indexed

  -- Extract the index from the found pair (if any)
  Option.map (fun (_, i) => i) found
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  -- !benchmark @start postcond
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findFirstOdd_spec_satisfied (a: Array Int) (h_precond : findFirstOdd_precond (a)) :
    findFirstOdd_postcond (a) (findFirstOdd (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findFirstOdd findFirstOdd_postcond
  let la := a.toList
  have h_la : la = a.toList := by rfl
  let indexed := la.zipIdx
  have h_indexed : indexed = la.zipIdx := by rfl
  let found := List.find? (fun (x, _) => isOdd x) indexed
  have h_found : found = List.find? (fun (x, _) => isOdd x) indexed := by rfl
  let res := Option.map (fun (_, i) => i) found
  have h_res : res = Option.map (fun (_, i) => i) found := by rfl
  simp_all
  cases h_rescase : res with
  | none =>
    rw [← h_res, h_rescase]
    simp
    rw [h_rescase] at h_res
    have h_notfound : found = none := by
      rw [h_found]
      exact Option.map_eq_none.mp h_rescase
    rw [List.find?_eq_none] at h_notfound
    simp at h_notfound
    intro i hi
    have hi' : i < la.length := by exact hi
    have h_mem : (la[i], i) ∈ indexed := by
      have : la[i]? = some la[i] := by
        exact (List.getElem?_eq_some_getElem_iff la i hi').mpr trivial
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp
    have hai : a[i]! = a[i] := by
      exact getElem!_pos a i hi'
    rw [hai]
    exact h_notfound a[i] i h_mem
  | some i =>
    rw [← h_res, h_rescase]
    rw [h_res] at h_rescase
    simp
    rw [Option.map_eq_some'] at h_rescase
    rcases h_rescase with ⟨p, ⟨h_found', hp⟩⟩
    have h_mem : p ∈ indexed := by
      exact List.mem_of_find?_eq_some h_found'
    have ⟨_, hi, hx⟩ := List.mem_zipIdx h_mem
    have ⟨h_odd, ⟨i', hi', hii', h_prefix⟩⟩ := List.find?_eq_some_iff_getElem.mp h_found'
    simp_all
    have hai : a[i]! = a[i] := by
      exact getElem!_pos a i hi
    rw [hai]
    constructor
    · exact h_odd
    · intro j hj
      have hii' : i = i' := by
        rw [← hii'] at hp
        simp_all
      have hj' : j < a.size := by
        exact Nat.lt_trans hj hi
      have haj : a[j]! = a[j] := by
        exact getElem!_pos a j hj'
      rw [haj]
      rw [hii'] at hj
      exact h_prefix j hj
  -- !benchmark @end proof
