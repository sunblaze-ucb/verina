-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  -- !benchmark @start code
  a.map (fun x => x * x * x)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def cubeElements_postcond (a : Array Int) (result: Array Int) (h_precond : cubeElements_precond (a)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem cubeElements_spec_satisfied (a: Array Int) (h_precond : cubeElements_precond (a)) :
    cubeElements_postcond (a) (cubeElements (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold cubeElements cubeElements_postcond
  simp_all
  intro i hi
  have h_maplen : (Array.map (fun x => x * x * x) a).size = a.size := by
    apply Array.size_map
  have h1 : (Array.map (fun x => x * x * x) a)[i] = (fun x => x * x * x) a[i] := by
    apply Array.getElem_map
  have h_eq : (Array.map (fun x => x * x * x) a)[i] = (Array.map (fun x => x * x * x) a)[i]! := by
    have hi' : i < (Array.map (fun x => x * x * x) a).size := by
      simp only [hi, h_maplen]
    rw [Array.getElem!_eq_getD]
    simp [hi', hi]
  rw [← h_eq]
  simp only [h1]
  have h_eq' : a[i] = a[i]! := by
    have hi_a : i < a.size := by
      simp only [hi]
    rw [Array.getElem!_eq_getD]
    simp [hi_a]
  simp only [h_eq']
  -- !benchmark @end proof
