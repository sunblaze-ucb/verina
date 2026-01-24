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
Fixpoint list_nodup_Z (l : list Z) : bool :=
  match l with
  | [] => true
  | h :: t => negb (existsb (fun x => x =? h) t) && list_nodup_Z t
  end.
(* !benchmark @end precond_aux *)

Definition nextGreaterElement_precond (nums1 : (list Z)) (nums2 : (list Z)) : bool :=
  (* !benchmark @start precond *)
  list_nodup_Z nums1 && list_nodup_Z nums2 && forallb (fun x => existsb (fun y => y =? x) nums2) nums1
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint nth_Z (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z t n'
  end.

Fixpoint processStack (nums2 : list Z) (s : list nat) (currentValue : Z) (m : list (Z * Z)) : list nat * list (Z * Z) :=
  match s with
  | [] => ([], m)
  | topIndex :: rest =>
      let topValue := nth_Z nums2 topIndex in
      if currentValue >? topValue then
        let newMap := (topValue, currentValue) :: m in
        processStack nums2 rest currentValue newMap
      else
        (s, m)
  end.

Fixpoint mapLoop (nums2 : list Z) (fuel : nat) (index : nat) (stack : list nat) (map : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => fold_left (fun acc pos => (nth_Z nums2 pos, -1) :: acc) stack map
  | S fuel' =>
      if (index <? length nums2)%nat then
        let currentValue := nth_Z nums2 index in
        let '(newStack, newMap) := processStack nums2 stack currentValue map in
        mapLoop nums2 fuel' (S index) (index :: newStack) newMap
      else
        fold_left (fun acc pos => (nth_Z nums2 pos, -1) :: acc) stack map
  end.

Definition buildNextGreaterMap (nums2 : list Z) : list (Z * Z) :=
  mapLoop nums2 (length nums2) O [] [].

Fixpoint findInMap (m : list (Z * Z)) (val : Z) : Z :=
  match m with
  | [] => -1
  | (num, nextGreater) :: rest =>
      if num =? val then nextGreater
      else findInMap rest val
  end.

Fixpoint resultLoop (nums1 : list Z) (ngMap : list (Z * Z)) (fuel : nat) (i : nat) (result : list Z) : list Z :=
  match fuel with
  | O => rev result
  | S fuel' =>
      if (i <? length nums1)%nat then
        let val := nth_Z nums1 i in
        let nextGreater := findInMap ngMap val in
        resultLoop nums1 ngMap fuel' (S i) (nextGreater :: result)
      else
        rev result
  end.
(* !benchmark @end code_aux *)

Definition nextGreaterElement (nums1 : (list Z)) (nums2 : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let ngMap := buildNextGreaterMap nums2 in
  resultLoop nums1 ngMap (length nums1) O []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint nth_Z_post (l : list Z) (n : nat) : Z :=
  match l, n with
  | [], _ => 0
  | h :: _, O => h
  | _ :: t, S n' => nth_Z_post t n'
  end.

Fixpoint findIdx_Z (l : list Z) (val : Z) (idx : nat) : option nat :=
  match l with
  | [] => None
  | h :: t => if h =? val then Some idx else findIdx_Z t val (S idx)
  end.

Fixpoint findNextGreaterOffset (nums2 : list Z) (idx : nat) (val : Z) (k : nat) (limit : nat) : option nat :=
  match limit with
  | O => None
  | S limit' =>
      let pos := (idx + k + 1)%nat in
      if (pos <? length nums2)%nat then
        if nth_Z_post nums2 pos >? val then Some k
        else findNextGreaterOffset nums2 idx val (S k) limit'
      else None
  end.

Definition checkOneResult (nums1 nums2 result : list Z) (i : nat) : bool :=
  let val := nth_Z_post nums1 i in
  let resultVal := nth_Z_post result i in
  match findIdx_Z nums2 val O with
  | None => false
  | Some idx =>
      let limit := (length nums2 - idx)%nat in
      match findNextGreaterOffset nums2 idx val O limit with
      | None => resultVal =? -1
      | Some offset => resultVal =? nth_Z_post nums2 (idx + offset + 1)%nat
      end
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.
(* !benchmark @end postcond_aux *)

Definition nextGreaterElement_postcond (nums1 : (list Z)) (nums2 : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  ((length result =? length nums1)%nat) &&
  (forallb (fun i => checkOneResult nums1 nums2 result i) (range (length nums1))) &&
  (forallb (fun val => (val =? -1) || existsb (fun y => y =? val) nums2) result)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem nextGreaterElement_postcond_satisfied (nums1 : (list Z)) (nums2 : (list Z)) :
    nextGreaterElement_precond nums1 nums2 = true ->
    nextGreaterElement_postcond nums1 nums2 (nextGreaterElement nums1 nums2) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
