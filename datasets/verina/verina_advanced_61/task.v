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

Definition productExceptSelf_precond (nums : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Definition getLast (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | _ => last l default
  end.

Fixpoint computePref (nums : list Z) (acc : list Z) : list Z :=
  match nums with
  | [] => acc
  | x :: xs => computePref xs (acc ++ [getLast acc 1 * x])
  end.

Definition computePrefixProducts (nums : list Z) : list Z :=
  computePref nums [1].

Fixpoint computeSuff (nums : list Z) (acc : list Z) : list Z :=
  match nums with
  | [] => acc
  | x :: xs => computeSuff xs (acc ++ [getLast acc 1 * x])
  end.

Definition computeSuffixProducts (nums : list Z) : list Z :=
  rev (computeSuff (rev nums) [1]).

Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | x :: _, O => x
  | _ :: xs, S n' => nth_Z xs n'
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.
(* !benchmark @end code_aux *)

Definition productExceptSelf (nums : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let n := length nums in
  match n with
  | O => []
  | _ =>
    let pref := computePrefixProducts nums in
    let suffix := computeSuffixProducts nums in
    map (fun i => nth_Z pref i * nth_Z suffix (S i)) (range n)
  end
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint list_prod (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * list_prod xs
  end.

Fixpoint take (n : nat) (l : list Z) : list Z :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: xs => x :: take n' xs
  end.

Fixpoint drop (n : nat) (l : list Z) : list Z :=
  match n, l with
  | O, l => l
  | _, [] => []
  | S n', _ :: xs => drop n' xs
  end.

Fixpoint nth_Z_opt (l : list Z) (n : nat) : option Z :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: xs, S n' => nth_Z_opt xs n'
  end.

Fixpoint range_nat (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range_nat n' ++ [n']
  end.

Definition check_index (nums result : list Z) (i : nat) : bool :=
  match nth_Z_opt result i with
  | None => false
  | Some r => (r =? (list_prod (take i nums) * list_prod (drop (S i) nums)))%Z
  end.
(* !benchmark @end postcond_aux *)

Definition productExceptSelf_postcond (nums : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  (length nums =? length result)%nat &&
  forallb (fun i => check_index nums result i) (range_nat (length nums))
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem productExceptSelf_postcond_satisfied (nums : (list Z)) :
    productExceptSelf_precond nums = true ->
    productExceptSelf_postcond nums (productExceptSelf nums) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
