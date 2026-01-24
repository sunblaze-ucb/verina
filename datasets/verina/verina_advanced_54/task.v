(* !benchmark @start import type=task *)
Require Import Nat.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint list_nodup_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | h :: t => negb (existsb (fun x => x =? h) t) && list_nodup_nat t
  end.
(* !benchmark @end precond_aux *)

Definition missingNumber_precond (nums : (list nat)) : bool :=
  (* !benchmark @start precond *)
  forallb (fun x => x <=? length nums) nums && list_nodup_nat nums
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => O
  | h :: t => (h + sum_list t)%nat
  end.
(* !benchmark @end code_aux *)

Definition missingNumber (nums : (list nat)) : nat :=
  (* !benchmark @start code *)
  let n := length nums in
  let expectedSum := (n * (n + 1)) / 2 in
  let actualSum := sum_list nums in
  (expectedSum - actualSum)%nat
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint range_nat (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range_nat n' ++ [n']
  end.
(* !benchmark @end postcond_aux *)

Definition missingNumber_postcond (nums : (list nat)) (result : nat) : bool :=
  (* !benchmark @start postcond *)
  let n := length nums in
  existsb (fun x => x =? result) (range_nat (n + 1)) &&
  negb (existsb (fun x => x =? result) nums) &&
  forallb (fun x => implb (negb (x =? result)) (existsb (fun y => y =? x) nums)) (range_nat (n + 1))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem missingNumber_postcond_satisfied (nums : (list nat)) :
    missingNumber_precond nums = true ->
    missingNumber_postcond nums (missingNumber nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
