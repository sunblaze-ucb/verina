(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Bool.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition mostFrequent_precond (xs : (list Z)) : bool :=
  (* !benchmark @start precond *)
  negb (match xs with [] => true | _ => false end)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Count occurrences of x in list *)
Fixpoint countZ (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (countZ x t) else countZ x t
  end.

(* Find the maximum count among all elements *)
Fixpoint maxCountAux (l : list Z) (original : list Z) (currentMax : nat) : nat :=
  match l with
  | [] => currentMax
  | h :: t => 
    let c := countZ h original in
    if (currentMax <? c)%nat then maxCountAux t original c
    else maxCountAux t original currentMax
  end.

Definition maxCount (l : list Z) : nat := maxCountAux l l O.

(* Find first element with the maximum count *)
Fixpoint firstWithMaxCount (l : list Z) (original : list Z) (maxC : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t => 
    if (countZ h original =? maxC)%nat then h
    else firstWithMaxCount t original maxC
  end.
(* !benchmark @end code_aux *)

Definition mostFrequent (xs : (list Z)) : Z :=
  (* !benchmark @start code *)
  let maxC := maxCount xs in
  firstWithMaxCount xs xs maxC
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Count occurrences of x in list - for postcond *)
Fixpoint countZ_post (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (countZ_post x t) else countZ_post x t
  end.

(* Check if result is in list *)
Fixpoint inListZ (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else inListZ x t
  end.

(* Check all elements have count <= result's count *)
Fixpoint allCountsLe (l : list Z) (original : list Z) (maxC : nat) : bool :=
  match l with
  | [] => true
  | h :: t => (countZ_post h original <=? maxC)%nat && allCountsLe t original maxC
  end.

(* Filter elements with specific count *)
Fixpoint filterByCount (l : list Z) (original : list Z) (c : nat) : list Z :=
  match l with
  | [] => []
  | h :: t => 
    if (countZ_post h original =? c)%nat then h :: filterByCount t original c
    else filterByCount t original c
  end.

(* Get head of list with default *)
Definition headZ (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: _ => h
  end.
(* !benchmark @end postcond_aux *)

Definition mostFrequent_postcond (xs : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let count := fun x => countZ_post x xs in
  let resultCount := count result in
  inListZ result xs &&
  allCountsLe xs xs resultCount &&
  (headZ (filterByCount xs xs resultCount) 0 =? result)%Z
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem mostFrequent_postcond_satisfied (xs : (list Z)) :
    mostFrequent_precond xs = true ->
    mostFrequent_postcond xs (mostFrequent xs) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
