(* !benchmark @start import type=task *)
Require Import List.
Require Import Nat.
Require Import Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)

(* !benchmark @end import *)

(* !benchmark @start task_aux *)

(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)

(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Fixpoint nth_default_list {A : Type} (default : list A) (l : list (list A)) (n : nat) : list A :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_list default t n'
              end
  end.
(* !benchmark @end precond_aux *)

Definition modify_array_element_precond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) : bool :=
  (* !benchmark @start precond *)
  (index1 <? length arr)%nat && (index2 <? length (nth_default_list [] arr index1))%nat
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint update_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match l with
  | [] => []
  | h :: t => match n with
              | O => v :: t
              | S n' => h :: update_nth t n' v
              end
  end.

Definition updateInner (a : list nat) (idx val : nat) : list nat :=
  update_nth a idx val.
(* !benchmark @end code_aux *)

Definition modify_array_element (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) : (list (list nat)) :=
  (* !benchmark @start code *)
  let inner := nth index1 arr [] in
    let inner' := updateInner inner index2 val in
    update_nth arr index1 inner'
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_default_nat (default : nat) (l : list nat) (n : nat) : nat :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_nat default t n'
              end
  end.

Fixpoint nth_default_list_post (default : list nat) (l : list (list nat)) (n : nat) : list nat :=
  match l with
  | [] => default
  | h :: t => match n with
              | O => h
              | S n' => nth_default_list_post default t n'
              end
  end.

Definition forallb_indexed {A : Type} (f : nat -> A -> bool) (l : list A) : bool :=
  (fix aux (n : nat) (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => andb (f n h) (aux (S n) t)
    end) O l.

Fixpoint list_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => andb (Nat.eqb h1 h2) (list_eqb t1 t2)
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition modify_array_element_postcond (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) (result : (list (list nat))) : bool :=
  (* !benchmark @start postcond *)
  andb (andb 
      (forallb_indexed (fun i _ => implb (andb (i <? length arr)%nat (negb (Nat.eqb i index1)))
                                         (list_eqb (nth_default_list_post [] result i) (nth_default_list_post [] arr i))) arr)
      (forallb_indexed (fun j _ => implb (andb (j <? length (nth_default_list_post [] arr index1))%nat (negb (Nat.eqb j index2)))
                                            (Nat.eqb (nth_default_nat 0 (nth_default_list_post [] result index1) j) (nth_default_nat 0 (nth_default_list_post [] arr index1) j))) (nth_default_list_post [] arr index1)))
      (Nat.eqb (nth_default_nat 0 (nth_default_list_post [] result index1) index2) val)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem modify_array_element_postcond_satisfied (arr : (list (list nat))) (index1 : nat) (index2 : nat) (val : nat) :
    modify_array_element_precond arr index1 index2 val = true ->
    modify_array_element_postcond arr index1 index2 val (modify_array_element arr index1 index2 val) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
