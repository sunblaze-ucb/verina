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

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)

(* !benchmark @end precond_aux *)

Definition task_code_precond (sequence : (list Z)) : bool :=
  (* !benchmark @start precond *)
  (1 <=? length sequence)%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition kadane_step (acc : Z * Z) (x : Z) : Z * Z :=
  let '(cur, maxSoFar) := acc in
  let newCur := if (cur + x >=? x)%Z then cur + x else x in
  let newMax := if (maxSoFar >=? newCur)%Z then maxSoFar else newCur in
  (newCur, newMax).
(* !benchmark @end code_aux *)

Definition task_code (sequence : (list Z)) : Z :=
  (* !benchmark @start code *)
  match sequence with
  | [] => 0
  | x :: xs =>
      let '(_, maxSoFar) := fold_left kadane_step xs (x, x) in
      maxSoFar
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2)%Z && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S k => range k ++ [k]
  end.

Definition drop {A : Type} (n : nat) (l : list A) : list A :=
  skipn n l.

Definition take {A : Type} (n : nat) (l : list A) : list A :=
  firstn n l.

Definition all_subarrays (seq : list Z) : list (list Z) :=
  let n := length seq in
  flat_map (fun start =>
    map (fun len => take len (drop start seq))
        (range (n - start + 1)%nat))
    (range (n + 1)%nat).

Definition non_empty_subarrays (seq : list Z) : list (list Z) :=
  filter (fun l => negb (list_Z_eqb l [])) (all_subarrays seq).

Definition subarray_sums (seq : list Z) : list Z :=
  map sum_list (non_empty_subarrays seq).
(* !benchmark @end postcond_aux *)

Definition task_code_postcond (sequence : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let sums := subarray_sums sequence in
  existsb (fun s => (s =? result)%Z) sums && forallb (fun s => (s <=? result)%Z) sums
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem task_code_postcond_satisfied (sequence : (list Z)) :
    task_code_precond sequence = true ->
    task_code_postcond sequence (task_code sequence) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
