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
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition productExceptSelf_precond_dec (nums : list Z) : bool :=
  true.
(* !benchmark @end precond_aux *)

Definition productExceptSelf_precond (nums : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper: Compute prefix products. *)
(* prefix[i] is the product of all elements in nums before index i. *)
Fixpoint computepref_aux (nums : list Z) (acc : list Z) (last : Z) : list Z :=
  match nums with
  | [] => acc
  | x :: xs => computepref_aux xs (acc ++ [last * x]) (last * x)
  end.

Definition computepref (nums : list Z) : list Z :=
  computepref_aux nums [1] 1.

(* Helper: Compute suffix products. *)
(* suffix[i] is the product of all elements in nums from index i (inclusive) to the end. *)
Fixpoint computeSuffix_aux (nums : list Z) (acc : list Z) (last : Z) : list Z :=
  match nums with
  | [] => acc
  | x :: xs => computeSuffix_aux xs (acc ++ [last * x]) (last * x)
  end.

Definition computeSuffix (nums : list Z) : list Z :=
  let revSuffix := computeSuffix_aux (rev nums) [1] 1 in
  rev revSuffix.

(* Helper to get nth element with default 0 *)
Definition get_nth (l : list Z) (n : nat) : Z :=
  nth n l 0.

(* Helper to generate range [0..n-1] *)
Fixpoint range_helper (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => acc
  | S n' => range_helper n' (n' :: acc)
  end.

Definition range (n : nat) : list nat :=
  range_helper n [].
(* !benchmark @end code_aux *)

Definition productExceptSelf (nums : (list Z)) (h_precond : productExceptSelf_precond nums) : (list Z) :=
  (* !benchmark @start code *)
  let n := length nums in
  if (n =? 0)%nat then []
  else
    let pref := computepref nums in
    let suffix := computeSuffix nums in
    map (fun i => (get_nth pref i) * (get_nth suffix (S i))) (range n)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Specification Helper: Product of a list of Ints *)
Fixpoint list_myprod (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * (list_myprod xs)
  end.

(* Helper to check if all elements in a list of bools are true *)
Fixpoint all_true (l : list bool) : bool :=
  match l with
  | [] => true
  | b :: bs => andb b (all_true bs)
  end.

(* Helper to get nth element as option *)
Definition get_nth_opt (l : list Z) (n : nat) : option Z :=
  nth_error l n.

Definition productExceptSelf_postcond_dec (nums : list Z) (result : list Z) : bool :=
  (length nums =? length result)%nat &&
  all_true (map (fun i =>
    match get_nth_opt result i with
    | Some r => (r =? (list_myprod (firstn i nums)) * (list_myprod (skipn (S i) nums)))%Z
    | None => false
    end) (range (length nums))).
(* !benchmark @end postcond_aux *)

Definition productExceptSelf_postcond (nums : (list Z)) (result : (list Z)) (h_precond : productExceptSelf_precond nums) : Prop :=
  (* !benchmark @start postcond *)
  (length nums = length result)%nat /\
  (forall i : nat, (i < length nums)%nat ->
    exists r : Z, nth_error result i = Some r /\
    r = (list_myprod (firstn i nums)) * (list_myprod (skipn (S i) nums)))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem productExceptSelf_postcond_satisfied (nums : (list Z)) (h_precond : productExceptSelf_precond nums) :
    productExceptSelf_postcond nums (productExceptSelf nums h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
