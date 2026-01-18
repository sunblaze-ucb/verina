(* !benchmark @start import type=task *)

(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* Map structure represented as list of pairs *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* Helper function to insert a key-value pair into a map *)
Definition insert (m : list (Z * Z)) (k : Z) (v : Z) : list (Z * Z) :=
  filter (fun p => negb (Z.eqb (fst p) k)) m ++ [(k, v)].

(* Merge sort for list of pairs by first component *)
Fixpoint merge_pairs (l1 l2 : list (Z * Z)) : list (Z * Z) :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | (k1, v1) :: t1, (k2, v2) :: t2 =>
      if Z.leb k1 k2
      then (k1, v1) :: merge_pairs t1 l2
      else (k2, v2) :: merge_pairs l1 t2
  end.

Fixpoint merge_sort_pairs_aux (fuel : nat) (l : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => l
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | _ =>
          let n := length l in
          let m := Nat.div n 2%nat in
          let l1 := firstn m l in
          let l2 := skipn m l in
          merge_pairs (merge_sort_pairs_aux fuel' l1) (merge_sort_pairs_aux fuel' l2)
      end
  end.

Definition merge_sort_pairs (l : list (Z * Z)) : list (Z * Z) :=
  merge_sort_pairs_aux (length l) l.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
Definition update_map_precond_dec (m1 : list (Z * Z)) (m2 : list (Z * Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition update_map_precond (m1 : list (Z * Z)) (m2 : list (Z * Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper function to find a value by key *)
Fixpoint find_opt (m : list (Z * Z)) (k : Z) : option Z :=
  match m with
  | [] => None
  | (k', v) :: rest => if Z.eqb k' k then Some v else find_opt rest k
  end.
(* !benchmark @end code_aux *)

Definition update_map (m1 : list (Z * Z)) (m2 : list (Z * Z)) (h_precond : update_map_precond m1 m2) : list (Z * Z) :=
  (* !benchmark @start code *)
  let updated := fold_left (fun acc entry => insert acc (fst entry) (snd entry)) m2 m1 in
merge_sort_pairs updated
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper: check if list is pairwise sorted by first component *)
Fixpoint pairwise_le_fst (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | (k1, _) :: ((k2, _) :: _) as rest =>
      k1 <= k2 /\ pairwise_le_fst rest
  end.

(* Helper: check if all entries in m satisfy a predicate *)
Fixpoint all_entries (m : list (Z * Z)) (P : Z * Z -> Prop) : Prop :=
  match m with
  | [] => True
  | x :: rest => P x /\ all_entries rest P
  end.

(* Helper: find function *)
Fixpoint find_in_map (m : list (Z * Z)) (k : Z) : option Z :=
  match m with
  | [] => None
  | (k', v) :: rest => if Z.eqb k' k then Some v else find_in_map rest k
  end.

(* Decidable versions *)
Fixpoint pairwise_le_fst_dec (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | [_] => true
  | (k1, _) :: ((k2, _) :: _) as rest =>
      Z.leb k1 k2 && pairwise_le_fst_dec rest
  end.

Fixpoint all_entries_dec (m : list (Z * Z)) (P : Z * Z -> bool) : bool :=
  match m with
  | [] => true
  | x :: rest => P x && all_entries_dec rest P
  end.

Definition update_map_postcond_dec (m1 : list (Z * Z)) (m2 : list (Z * Z)) (result : list (Z * Z)) : bool :=
  pairwise_le_fst_dec result &&
  all_entries_dec m2 (fun x => match find_in_map result (fst x) with
                                | Some v => Z.eqb v (snd x)
                                | None => false
                                end) &&
  all_entries_dec m1 (fun x => match find_in_map m2 (fst x) with
                                | Some _ => true
                                | None => match find_in_map result (fst x) with
                                         | Some v => Z.eqb v (snd x)
                                         | None => false
                                         end
                                end) &&
  all_entries_dec result (fun x =>
    match find_in_map m1 (fst x) with
    | Some v => match find_in_map m2 (fst x) with
                | Some v' => Z.eqb (snd x) v'
                | None => Z.eqb (snd x) v
                end
    | None => match find_in_map m2 (fst x) with
              | Some v => Z.eqb (snd x) v
              | None => false
              end
    end).
(* !benchmark @end postcond_aux *)

Definition update_map_postcond (m1 : list (Z * Z)) (m2 : list (Z * Z)) (result : list (Z * Z)) (h_precond : update_map_precond m1 m2) : Prop :=
  (* !benchmark @start postcond *)
  pairwise_le_fst result /\
all_entries m2 (fun x => find_in_map result (fst x) = Some (snd x)) /\
all_entries m1 (fun x =>
  match find_in_map m2 (fst x) with
  | Some _ => True
  | None => find_in_map result (fst x) = Some (snd x)
  end) /\
all_entries result (fun x =>
  match find_in_map m1 (fst x) with
  | Some v => match find_in_map m2 (fst x) with
              | Some v' => snd x = v'
              | None => snd x = v
              end
  | None => find_in_map m2 (fst x) = Some (snd x)
  end)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem update_map_postcond_satisfied (m1 : list (Z * Z)) (m2 : list (Z * Z)) (h_precond : update_map_precond m1 m2) :
    update_map_postcond m1 m2 (update_map m1 m2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
