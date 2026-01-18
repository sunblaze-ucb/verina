(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Lia.
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition list_nth_Z (l : list Z) (n : nat) : option Z :=
  nth_error l n.

Fixpoint list_has_distinct (l : list Z) : Prop :=
  match l with
  | [] => False
  | x :: xs => 
    (exists y, In y xs /\ x <> y) \/ list_has_distinct xs
  end.

Definition secondSmallest_precond_dec (s : list Z) : bool :=
  (Nat.ltb 1%nat (length s)) &&
  (let fix has_distinct_dec (l : list Z) (fuel : nat) : bool :=
    match fuel with
    | O => false
    | S n' =>
      match l with
      | [] => false
      | x :: xs =>
        orb (existsb (fun y => negb (Z.eqb x y)) xs) (has_distinct_dec xs n')
      end
    end in
  has_distinct_dec s (length s)).
(* !benchmark @end precond_aux *)

Definition secondSmallest_precond (s : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  (length s > 1)%nat /\ (exists i j, (i < length s)%nat /\ (j < length s)%nat /\ 
  match list_nth_Z s i, list_nth_Z s j with
  | Some vi, Some vj => vi <> vj
  | _, _ => False
  end)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)
Fixpoint secondSmallestAux (s : list Z) (i minIdx secondIdx : nat) (fuel : nat) : Z :=
  match fuel with
  | O => match list_nth_Z s secondIdx with Some v => v | None => 0%Z end
  | S fuel' =>
    if (i >=? length s)%nat then
      match list_nth_Z s secondIdx with Some v => v | None => 0%Z end
    else
      match list_nth_Z s i, list_nth_Z s minIdx, list_nth_Z s secondIdx with
      | Some x, Some m, Some smin =>
        if (x <? m)%Z then
          secondSmallestAux s (i + 1)%nat i minIdx fuel'
        else if (x <? smin)%Z then
          secondSmallestAux s (i + 1)%nat minIdx i fuel'
        else
          secondSmallestAux s (i + 1)%nat minIdx secondIdx fuel'
      | _, _, _ => 0%Z
      end
  end.
(* !benchmark @end code_aux *)

Definition secondSmallest (s : (list Z)) (h_precond : secondSmallest_precond s) : Z :=
  (* !benchmark @start code *)
  match list_nth_Z s 0%nat, list_nth_Z s 1%nat with
| Some v0, Some v1 =>
  let minIdx := if (v1 <? v0)%Z then 1%nat else 0%nat in
  let secondIdx := if (v1 <? v0)%Z then 0%nat else 1%nat in
  secondSmallestAux s 2%nat minIdx secondIdx (length s)
| _, _ => 0%Z
end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)
Definition secondSmallest_postcond_dec (s : list Z) (result : Z) : bool :=
  (existsb (fun x => Z.eqb x result) s) &&
  (existsb (fun x => 
    andb (x <? result)%Z
    (forallb (fun y => 
      orb (Z.eqb y x) (y >=? result)%Z
    ) s)
  ) s).
(* !benchmark @end postcond_aux *)

Definition secondSmallest_postcond (s : (list Z)) (result : Z) (h_precond : secondSmallest_precond s) : Prop :=
  (* !benchmark @start postcond *)
  (exists i, (i < length s)%nat /\ 
  match list_nth_Z s i with Some v => v = result | None => False end) /\
(exists j, (j < length s)%nat /\ 
  match list_nth_Z s j with 
  | Some vj => (vj < result)%Z /\ 
    (forall k, (k < length s)%nat -> 
      match list_nth_Z s k with
      | Some vk => vk <> vj -> (vk >= result)%Z
      | None => True
      end)
  | None => False
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem secondSmallest_postcond_satisfied (s : (list Z)) (h_precond : secondSmallest_precond s) :
    secondSmallest_postcond s (secondSmallest s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
