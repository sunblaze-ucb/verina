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
(* Map is represented as list (Z * Z) *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* find? helper - used by both code logic and postcond *)
Fixpoint find_opt (m : list (Z * Z)) (k : Z) : option Z :=
  match m with
  | [] => None
  | (k', v') :: rest => if (k' =? k)%Z then Some v' else find_opt rest k
  end.
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* no helpers needed *)
(* !benchmark @end precond_aux *)

Definition update_map_precond (m1 : list (Z * Z)) (m2 : list (Z * Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* insert into map - removes existing key first, then appends *)
Fixpoint filter_key (m : list (Z * Z)) (k : Z) : list (Z * Z) :=
  match m with
  | [] => []
  | (k', v') :: rest => 
      if (k' =? k)%Z then filter_key rest k
      else (k', v') :: filter_key rest k
  end.

Definition insert_map (m : list (Z * Z)) (k : Z) (v : Z) : list (Z * Z) :=
  filter_key m k ++ [(k, v)].

(* fold over m2 to insert into m1 *)
Fixpoint fold_insert (acc : list (Z * Z)) (entries : list (Z * Z)) : list (Z * Z) :=
  match entries with
  | [] => acc
  | (k, v) :: rest => fold_insert (insert_map acc k v) rest
  end.

(* merge with fuel to ensure termination *)
Fixpoint merge_fuel (fuel : nat) (l1 l2 : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => l1 ++ l2
  | S fuel' =>
      match l1, l2 with
      | [], _ => l2
      | _, [] => l1
      | (k1, v1) :: t1, (k2, v2) :: t2 =>
          if (k1 <=? k2)%Z then (k1, v1) :: merge_fuel fuel' t1 l2
          else (k2, v2) :: merge_fuel fuel' l1 t2
      end
  end.

Definition merge (l1 l2 : list (Z * Z)) : list (Z * Z) :=
  merge_fuel (length l1 + length l2) l1 l2.

Fixpoint split_list (l : list (Z * Z)) : (list (Z * Z) * list (Z * Z)) :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      let (l1, l2) := split_list rest in
      (x :: l1, y :: l2)
  end.

Fixpoint merge_sort_fuel (fuel : nat) (l : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => l
  | S fuel' =>
      match l with
      | [] => []
      | [x] => [x]
      | _ =>
          let (l1, l2) := split_list l in
          merge (merge_sort_fuel fuel' l1) (merge_sort_fuel fuel' l2)
      end
  end.

Definition merge_sort (l : list (Z * Z)) : list (Z * Z) :=
  merge_sort_fuel (length l) l.
(* !benchmark @end code_aux *)

Definition update_map (m1 : list (Z * Z)) (m2 : list (Z * Z)) : list (Z * Z) :=
  (* !benchmark @start code *)
  let updated := fold_insert m1 m2 in
  merge_sort updated
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Check if list is sorted by first element (pairwise) *)
Fixpoint is_sorted (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | [_] => true
  | (k1, _) :: ((k2, v2) :: rest as tail) => (k1 <=? k2)%Z && is_sorted tail
  end.

(* option Z equality *)
Definition option_Z_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with
  | None, None => true
  | Some v1, Some v2 => (v1 =? v2)%Z
  | _, _ => false
  end.
(* !benchmark @end postcond_aux *)

Definition update_map_postcond (m1 : list (Z * Z)) (m2 : list (Z * Z)) (result : list (Z * Z)) : bool :=
  (* !benchmark @start postcond *)
  is_sorted result &&
  forallb (fun entry : Z * Z => let (k, v) := entry in option_Z_eqb (find_opt result k) (Some v)) m2 &&
  forallb (fun entry : Z * Z => 
    let (k, v) := entry in
    match find_opt m2 k with
    | Some _ => true
    | None => option_Z_eqb (find_opt result k) (Some v)
    end) m1 &&
  forallb (fun entry : Z * Z =>
    let (k, v) := entry in
    match find_opt m1 k with
    | Some v1 =>
        match find_opt m2 k with
        | Some v2 => (v =? v2)%Z
        | None => (v =? v1)%Z
        end
    | None => option_Z_eqb (find_opt m2 k) (Some v)
    end) result
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem update_map_postcond_satisfied (m1 : list (Z * Z)) (m2 : list (Z * Z)) :
    update_map_precond m1 m2 = true ->
    update_map_postcond m1 m2 (update_map m1 m2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
