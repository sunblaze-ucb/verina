(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
Fixpoint list_contains_Z (l : list Z) (x : Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (h =? x)%Z then true else list_contains_Z t x
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition firstDuplicate_precond (lst : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint helper (seen : list Z) (rem : list Z) : option Z :=
  match rem with
  | [] => None
  | h :: t => if list_contains_Z seen h then Some h else helper (h :: seen) t
  end.
(* !benchmark @end code_aux *)

Definition firstDuplicate (lst : (list Z)) : (option Z) :=
  (* !benchmark @start code *)
  helper [] lst
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint count_Z (l : list Z) (x : Z) : nat :=
  match l with
  | [] => O
  | h :: t => if (h =? x)%Z then S (count_Z t x) else count_Z t x
  end.

Fixpoint nodup_Z (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => negb (list_contains_Z t h) && nodup_Z t
  end.

Definition filter_Z (f : Z -> bool) (l : list Z) : list Z :=
  fold_right (fun x acc => if f x then x :: acc else acc) [] l.

Definition head_opt_Z (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Definition option_Z_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => (x =? y)%Z
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition firstDuplicate_postcond (lst : (list Z)) (result : (option Z)) : bool :=
  (* !benchmark @start postcond *)
  match result with
  | None => nodup_Z lst
  | Some x =>
      (1 <? count_Z lst x)%nat &&
      option_Z_eqb (head_opt_Z (filter_Z (fun y => (1 <? count_Z lst y)%nat) lst)) (Some x)
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem firstDuplicate_postcond_satisfied (lst : (list Z)) :
    firstDuplicate_precond lst = true ->
    firstDuplicate_postcond lst (firstDuplicate lst) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
