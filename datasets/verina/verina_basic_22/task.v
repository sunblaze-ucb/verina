(* !benchmark @start import type=task *)
Require Import ZArith.
Require Import List.
Require Import Bool.
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

Definition dissimilarElements_precond (a : (list Z)) (b : (list Z)) : bool :=
  (* !benchmark @start precond *)
  true
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
Fixpoint inList (a : list Z) (x : Z) : bool :=
  match a with
  | [] => false
  | h :: t => if (h =? x)%Z then true else inList t x
  end.

Fixpoint insertIfNotPresent (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if (x =? h)%Z then l else h :: insertIfNotPresent x t
  end.

Fixpoint collectDissimilarFromA (a b acc : list Z) : list Z :=
  match a with
  | [] => acc
  | h :: t => 
    if negb (inList b h) then collectDissimilarFromA t b (insertIfNotPresent h acc)
    else collectDissimilarFromA t b acc
  end.

Fixpoint collectDissimilarFromB (b a acc : list Z) : list Z :=
  match b with
  | [] => acc
  | h :: t => 
    if negb (inList a h) then collectDissimilarFromB t a (insertIfNotPresent h acc)
    else collectDissimilarFromB t a acc
  end.

Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if (x <=? h)%Z then x :: h :: t else h :: insert_sorted x t
  end.

Fixpoint insertion_sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (insertion_sort t)
  end.
(* !benchmark @end code_aux *)

Definition dissimilarElements (a : (list Z)) (b : (list Z)) : (list Z) :=
  (* !benchmark @start code *)
  let res1 := collectDissimilarFromA a b [] in
  let res2 := collectDissimilarFromB b a res1 in
  insertion_sort res2
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
Fixpoint inListBool (a : list Z) (x : Z) : bool :=
  match a with
  | [] => false
  | h :: t => if (h =? x)%Z then true else inListBool t x
  end.

Fixpoint pairwise_le (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: ((h2 :: _) as t) => (h1 <=? h2)%Z && pairwise_le t
  end.
(* !benchmark @end postcond_aux *)

Definition dissimilarElements_postcond (a : (list Z)) (b : (list Z)) (result : (list Z)) : bool :=
  (* !benchmark @start postcond *)
  forallb (fun x => negb (Bool.eqb (inListBool a x) (inListBool b x))) result &&
  pairwise_le result &&
  forallb (fun x => if inListBool b x then negb (inListBool result x) else inListBool result x) a &&
  forallb (fun x => if inListBool a x then negb (inListBool result x) else inListBool result x) b
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem dissimilarElements_postcond_satisfied (a : (list Z)) (b : (list Z)) :
    dissimilarElements_precond a b = true ->
    dissimilarElements_postcond a b (dissimilarElements a b) = true.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
