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

Definition uniqueProduct_precond (arr : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint Z_eqb_list (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (x =? h)%Z then true else Z_eqb_list x t
  end.

Fixpoint eraseDups_acc (l : list Z) (acc : list Z) : list Z :=
  match l with
  | [] => rev acc
  | h :: t => if Z_eqb_list h acc then eraseDups_acc t acc else eraseDups_acc t (h :: acc)
  end.

Definition eraseDups (l : list Z) : list Z := eraseDups_acc l [].

Definition foldl_product (l : list Z) : Z :=
  fold_left (fun acc x => acc * x) l 1.
(* !benchmark @end code_aux *)

Definition uniqueProduct (arr : (list Z)) : Z :=
  (* !benchmark @start code *)
  foldl_product (eraseDups arr)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint Z_eqb_list_post (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if (x =? h)%Z then true else Z_eqb_list_post x t
  end.

Fixpoint eraseDups_acc_post (l : list Z) (acc : list Z) : list Z :=
  match l with
  | [] => rev acc
  | h :: t => if Z_eqb_list_post h acc then eraseDups_acc_post t acc else eraseDups_acc_post t (h :: acc)
  end.

Definition eraseDups_post (l : list Z) : list Z := eraseDups_acc_post l [].

Definition foldl_product_post (l : list Z) : Z :=
  fold_left (fun acc x => acc * x) l 1.
(* !benchmark @end postcond_aux *)

Definition uniqueProduct_postcond (arr : (list Z)) (result : Z) : bool :=
  (* !benchmark @start postcond *)
  let expected := foldl_product_post (eraseDups_post arr) in
  ((result - expected =? 0)%Z && (expected - result =? 0)%Z)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem uniqueProduct_postcond_satisfied (arr : (list Z)) :
    uniqueProduct_precond arr = true ->
    uniqueProduct_postcond arr (uniqueProduct arr) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
