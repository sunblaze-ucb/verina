(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition findMajorityElement_precond (lst : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint countOccurrences (n : Z) (lst : list Z) : nat :=
  match lst with
  | [] => O
  | x :: xs => if (x =? n)%Z then S (countOccurrences n xs) else countOccurrences n xs
  end.

Fixpoint findMajorityHelper (candidates : list Z) (lst : list Z) (halfLen : nat) : option Z :=
  match candidates with
  | [] => None
  | x :: xs => 
    if (halfLen <? countOccurrences x lst)%nat 
    then Some x 
    else findMajorityHelper xs lst halfLen
  end.
(* !benchmark @end code_aux *)

Definition findMajorityElement (lst : (list Z)) : Z :=
  (* !benchmark @start code *)
  let n := length lst in
  let halfLen := Nat.div n 2 in
  match findMajorityHelper lst lst halfLen with
  | Some x => x
  | None => -1
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint countZ (x : Z) (lst : list Z) : nat :=
  match lst with
  | [] => O
  | y :: ys => if (y =? x)%Z then S (countZ x ys) else countZ x ys
  end.

Definition majorityCheck (result : Z) (lst : list Z) : bool :=
  let n := length lst in
  let halfLen := Nat.div n 2 in
  andb (halfLen <? countZ result lst)%nat 
       (forallb (fun x => orb (countZ x lst <=? halfLen)%nat (x =? result)%Z) lst).

Definition noMajorityExists (lst : list Z) : bool :=
  let n := length lst in
  let halfLen := Nat.div n 2 in
  forallb (fun x => (countZ x lst <=? halfLen)%nat) lst.
(* !benchmark @end postcond_aux *)

Definition findMajorityElement_postcond (lst : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let count := fun x => countZ x lst in
    let n := length lst in
    let halfLen := Nat.div n 2 in
    andb (implb (result =? -1)%Z (orb (noMajorityExists lst) (majorityCheck result lst)))
         (implb (negb (result =? -1)%Z) (majorityCheck result lst))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findMajorityElement_postcond_satisfied (lst : (list Z)) :
    findMajorityElement_precond lst = true ->
    findMajorityElement_postcond lst (findMajorityElement lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
