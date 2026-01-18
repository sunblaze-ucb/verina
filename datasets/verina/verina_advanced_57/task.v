(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
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
Fixpoint nodup_Z (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (Z.eqb x) xs) && nodup_Z xs
  end.

Fixpoint all_in (nums1 nums2 : list Z) : bool :=
  forallb (fun x => existsb (Z.eqb x) nums2) nums1.

Definition nextGreaterElement_precond_dec (nums1 : list Z) (nums2 : list Z) : bool :=
  nodup_Z nums1 && nodup_Z nums2 && all_in nums1 nums2.
(* !benchmark @end precond_aux *)

Definition nextGreaterElement_precond (nums1 : (list Z)) (nums2 : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  NoDup nums1 /\ NoDup nums2 /\ forallb (fun x => existsb (Z.eqb x) nums2) nums1 = true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint processStack (nums2 : list Z) (currentValue : Z) (s : list nat) (m : list (Z * Z)) : list nat * list (Z * Z) :=
  match s with
  | [] => ([], m)
  | topIndex :: rest =>
      match nth_error nums2 topIndex with
      | None => (s, m)
      | Some topValue =>
          if (currentValue >? topValue)%Z then
            let newMap := (topValue, currentValue) :: m in
            processStack nums2 currentValue rest newMap
          else
            (s, m)
      end
  end.

Fixpoint mapLoop (nums2 : list Z) (index : nat) (stack : list nat) (map : list (Z * Z)) (fuel : nat) : list (Z * Z) :=
  match fuel with
  | O => fold_left (fun acc pos => match nth_error nums2 pos with
                                    | Some v => (v, -1) :: acc
                                    | None => acc
                                    end) stack map
  | S fuel' =>
      if (index >=? length nums2)%nat then
        fold_left (fun acc pos => match nth_error nums2 pos with
                                  | Some v => (v, -1) :: acc
                                  | None => acc
                                  end) stack map
      else
        match nth_error nums2 index with
        | None => map
        | Some currentValue =>
            let '(newStack, newMap) := processStack nums2 currentValue stack map in
            mapLoop nums2 (index + 1)%nat (index :: newStack) newMap fuel'
        end
  end.

Fixpoint findInMap (val : Z) (m : list (Z * Z)) : Z :=
  match m with
  | [] => -1
  | (num, nextGreater) :: rest =>
      if (num =? val)%Z then nextGreater
      else findInMap val rest
  end.

Fixpoint resultLoop (nums1 : list Z) (buildNextGreaterMap : list (Z * Z)) (i : nat) (result : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => rev result
  | S fuel' =>
      if (i >=? length nums1)%nat then
        rev result
      else
        match nth_error nums1 i with
        | None => rev result
        | Some val =>
            let nextGreater := findInMap val buildNextGreaterMap in
            resultLoop nums1 buildNextGreaterMap (i + 1)%nat (nextGreater :: result) fuel'
        end
  end.
(* !benchmark @end code_aux *)

Definition nextGreaterElement (nums1 : (list Z)) (nums2 : (list Z)) (h_precond : nextGreaterElement_precond nums1 nums2) : (list Z) :=
  (* !benchmark @start code *)
  let buildNextGreaterMap := mapLoop nums2 0%nat [] [] (length nums2) in
resultLoop nums1 buildNextGreaterMap 0%nat [] (length nums1)
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint findIdx_Z (l : list Z) (x : Z) (idx : nat) : option nat :=
  match l with
  | [] => None
  | y :: ys => if (y =? x)%Z then Some idx else findIdx_Z ys x (idx + 1)%nat
  end.

Fixpoint find_next_greater (nums2 : list Z) (val : Z) (start : nat) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      match nth_error nums2 start with
      | None => None
      | Some v =>
          if (v >? val)%Z then Some v
          else find_next_greater nums2 val (start + 1)%nat fuel'
      end
  end.

Fixpoint check_all_indices (nums1 nums2 result : list Z) (i : nat) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if (i >=? length nums1)%nat then true
      else
        match nth_error nums1 i, nth_error result i with
        | Some val, Some resultVal =>
            match findIdx_Z nums2 val 0%nat with
            | None => false
            | Some idx =>
                match find_next_greater nums2 val (idx + 1)%nat (length nums2) with
                | None => (resultVal =? -1)%Z && check_all_indices nums1 nums2 result (i + 1)%nat fuel'
                | Some nextGreater => (resultVal =? nextGreater)%Z && check_all_indices nums1 nums2 result (i + 1)%nat fuel'
                end
            end
        | _, _ => false
        end
  end.

Fixpoint all_in_or_neg1 (result nums2 : list Z) : bool :=
  forallb (fun val => (val =? -1)%Z || existsb (Z.eqb val) nums2) result.

Definition nextGreaterElement_postcond_dec (nums1 : list Z) (nums2 : list Z) (result : list Z) : bool :=
  (length result =? length nums1)%nat &&
  check_all_indices nums1 nums2 result 0%nat (length nums1) &&
  all_in_or_neg1 result nums2.
(* !benchmark @end postcond_aux *)

Definition nextGreaterElement_postcond (nums1 : (list Z)) (nums2 : (list Z)) (result : (list Z)) (h_precond : nextGreaterElement_precond nums1 nums2) : Prop :=
  (* !benchmark @start postcond *)
  length result = length nums1 /\
check_all_indices nums1 nums2 result 0%nat (length nums1) = true /\
all_in_or_neg1 result nums2 = true
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem nextGreaterElement_postcond_satisfied (nums1 : (list Z)) (nums2 : (list Z)) (h_precond : nextGreaterElement_precond nums1 nums2) :
    nextGreaterElement_postcond nums1 nums2 (nextGreaterElement nums1 nums2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
