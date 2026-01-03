(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import FSets.FMapList.
Require Import FSets.FMapFacts.
Require Import Structures.OrderedTypeEx.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
Module Map := FMapList.Make(Z_as_OT).
Definition Int := Z.
(* !benchmark @end task_aux *)

(* !benchmark @start precond_aux *)
Definition update_map_precond_dec (m1 : Map.t Int) (m2 : Map.t Int) : bool := true.
(* !benchmark @end precond_aux *)

Definition update_map_precond (m1 : Map.t Int) (m2 : Map.t Int) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* !benchmark @end code_aux *)

Definition update_map (m1 : Map.t Int) (m2 : Map.t Int) (h_precond : update_map_precond m1 m2) : Map.t Int :=
  (* !benchmark @start code *)
  (* placeholder *) Map.empty Int
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Definition update_map_postcond_dec (m1 : Map.t Int) (m2 : Map.t Int) (result : Map.t Int) : bool := true.
(* !benchmark @end postcond_aux *)

Definition update_map_postcond (m1 : Map.t Int) (m2 : Map.t Int) (result : Map.t Int) (h_precond : update_map_precond m1 m2) : Prop :=
  (* !benchmark @start postcond *)
  True
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)
(* !benchmark @end proof_aux *)

Theorem update_map_postcond_satisfied (m1 : Map.t Int) (m2 : Map.t Int) (h_precond : update_map_precond m1 m2) :
    update_map_postcond m1 m2 (update_map m1 m2 h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.