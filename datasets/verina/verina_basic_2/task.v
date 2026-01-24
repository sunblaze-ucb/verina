(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition findSmallest_precond (s : (list nat)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint list_min (s : list nat) : option nat :=
  match s with
  | [] => None
  | [x] => Some x
  | x :: xs => match list_min xs with
               | None => Some x
               | Some m => Some (min x m)
               end
  end.
(* !benchmark @end code_aux *)

Definition findSmallest (s : (list nat)) : (option nat) :=
  (* !benchmark @start code *)
  list_min s
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint forallb_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => true
  | h :: t => f h && forallb_nat f t
  end.

Fixpoint existsb_nat (f : nat -> bool) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => f h || existsb_nat f t
  end.

Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (h1 =? h2)%nat && list_nat_eqb t1 t2
  | _, _ => false
  end.

Definition mem_nat (x : nat) (l : list nat) : bool :=
  existsb_nat (fun y => (y =? x)%nat) l.
(* !benchmark @end postcond_aux *)

Definition findSmallest_postcond (s : (list nat)) (result : (option nat)) : bool :=
  (* !benchmark @start postcond *)
  match result with
  | None => list_nat_eqb s []
  | Some r => mem_nat r s && forallb_nat (fun x => (r <=? x)%nat) s
  end
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem findSmallest_postcond_satisfied (s : (list nat)) :
    findSmallest_precond s = true ->
    findSmallest_postcond s (findSmallest s) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
