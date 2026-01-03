(* !benchmark @start import type=task *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition nextGreaterElement_precond_dec (nums1 : (list Z)) (nums2 : (list Z)) : bool := true.
(* !benchmark @end precond_aux *)

Definition nextGreaterElement_precond (nums1 : (list Z)) (nums2 : (list Z)) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition nextGreaterElement (nums1 : (list Z)) (nums2 : (list Z)) (h_precond : nextGreaterElement_precond nums1 nums2) : (list Z) :=
  (* !benchmark @start code *)
  []
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition nextGreaterElement_postcond_dec (nums1 : (list Z)) (nums2 : (list Z)) (result : (list Z)) : bool := true.
(* !benchmark @end postcond_aux *)

Definition nextGreaterElement_postcond (nums1 : (list Z)) (nums2 : (list Z)) (result : (list Z)) (h_precond : nextGreaterElement_precond nums1 nums2) : Prop :=
  (* !benchmark @start postcond *)
  True
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
