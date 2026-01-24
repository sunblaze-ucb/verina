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
Definition isEven (n : Z) : bool :=
  (n mod 2 =? 0)%Z.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition findEvenNumbers_precond (arr : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition findEvenNumbers (arr : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  filter isEven arr
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint idxOf (x : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then O else S (idxOf x t)
  end.

Fixpoint inListZ (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else inListZ x t
  end.
(* !benchmark @end postcond_aux *)

Definition findEvenNumbers_postcond (arr : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  andb (andb 
    (forallb (fun x => andb (isEven x) (inListZ x arr)) result)
    (forallb (fun x => implb (isEven x) (inListZ x result)) arr))
    (forallb (fun x => 
      forallb (fun y => 
        implb (andb (andb (andb (andb (inListZ x arr) (inListZ y arr)) (isEven x)) (isEven y)) ((idxOf x arr <=? idxOf y arr)%nat))
              ((idxOf x result <=? idxOf y result)%nat)
      ) arr
    ) arr)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findEvenNumbers_postcond_satisfied (arr : (list Z)) :
    findEvenNumbers_precond arr = true ->
    findEvenNumbers_postcond arr (findEvenNumbers arr) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
