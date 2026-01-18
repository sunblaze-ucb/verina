(* !benchmark @start import type=task *)
Require Import Bool.
Require Import List.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)

Fixpoint all_chords_valid (chords : list (list nat)) (N : nat) : Prop :=
  match chords with
  | [] => True
  | chord :: rest =>
      (length chord = 2%nat) /\
      (exists a b, chord = [a; b] /\ (1 <= a)%nat /\ (a <= 2 * N)%nat /\ (1 <= b)%nat /\ (b <= 2 * N)%nat) /\
      all_chords_valid rest N
  end.

Fixpoint all_chords_valid_dec (chords : list (list nat)) (N : nat) : bool :=
  match chords with
  | [] => true
  | chord :: rest =>
      match chord with
      | [a; b] => 
          (Nat.leb 1%nat a) && (Nat.leb a (2 * N)%nat) && 
          (Nat.leb 1%nat b) && (Nat.leb b (2 * N)%nat) &&
          all_chords_valid_dec rest N
      | _ => false
      end
  end.

Fixpoint flatten (l : list (list nat)) : list nat :=
  match l with
  | [] => []
  | x :: xs => x ++ flatten xs
  end.

Fixpoint nodup (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~In x xs /\ nodup xs
  end.

Fixpoint nodup_dec (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (Nat.eqb x) xs) && nodup_dec xs
  end.

Definition hasChordIntersection_precond_dec (N : nat) (chords : list (list nat)) : bool :=
  (Nat.leb 2%nat N) && all_chords_valid_dec chords N && nodup_dec (flatten chords).
(* !benchmark @end precond_aux *)

Definition hasChordIntersection_precond (N : nat) (chords : (list (list nat))) : Prop :=
  (* !benchmark @start precond *)
  (N >= 2)%nat /\
  all_chords_valid chords N /\
  nodup (flatten chords)
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* complete helper function definitions *)

Definition normalize_chord (chord : list nat) : list nat :=
  match chord with
  | [a; b] => if Nat.ltb b a then [b; a] else [a; b]
  | _ => chord
  end.

Fixpoint map_normalize (chords : list (list nat)) : list (list nat) :=
  match chords with
  | [] => []
  | c :: cs => normalize_chord c :: map_normalize cs
  end.

Fixpoint insert_chord (x : list nat) (xs : list (list nat)) : list (list nat) :=
  match x, xs with
  | [a; _], [] => [x]
  | [xa; _], (([ya; yb] :: ys) as full) => 
      if Nat.ltb xa ya then x :: full else [ya; yb] :: insert_chord x ys
  | _, _ => x :: xs
  end.

Fixpoint sort_chords (xs : list (list nat)) : list (list nat) :=
  match xs with
  | [] => []
  | x :: xs' => insert_chord x (sort_chords xs')
  end.

Fixpoint dropWhile (f : list nat -> bool) (stack : list (list nat)) : list (list nat) :=
  match stack with
  | [] => []
  | x :: xs => if f x then dropWhile f xs else stack
  end.

Fixpoint checkIntersection (stack : list (list nat)) (remaining : list (list nat)) : bool :=
  match remaining with
  | [] => false
  | chord :: rest =>
      match chord with
      | [a; b] =>
          let newStack := dropWhile (fun c => match c with | [_; cb] => Nat.ltb cb a | _ => false end) stack in
          match newStack with
          | [] => checkIntersection (chord :: newStack) rest
          | top :: _ =>
              match top with
              | [_; tb] =>
                  if (Nat.ltb a tb && Nat.ltb tb b) then true
                  else checkIntersection (chord :: newStack) rest
              | _ => false
              end
          end
      | _ => false
      end
  end.
(* !benchmark @end code_aux *)

Definition hasChordIntersection (N : nat) (chords : (list (list nat))) (h_precond : hasChordIntersection_precond N chords) : bool :=
  (* !benchmark @start code *)
  let sortedChords := map_normalize chords in
  let sortedChords := sort_chords sortedChords in
  checkIntersection [] sortedChords
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* postcondition helpers including _dec version, complete definitions *)

Definition has_intersection_chord (chord1 chord2 : list nat) : Prop :=
  match chord1, chord2 with
  | [a1; b1], [a2; b2] =>
      ((a1 < a2)%nat /\ (a2 < b1)%nat /\ (b1 < b2)%nat) \/
      ((a2 < a1)%nat /\ (a1 < b2)%nat /\ (b2 < b1)%nat)
  | _, _ => False
  end.

Definition has_intersection_chord_dec (chord1 chord2 : list nat) : bool :=
  match chord1, chord2 with
  | [a1; b1], [a2; b2] =>
      ((Nat.ltb a1 a2 && Nat.ltb a2 b1 && Nat.ltb b1 b2) ||
       (Nat.ltb a2 a1 && Nat.ltb a1 b2 && Nat.ltb b2 b1))
  | _, _ => false
  end.

Fixpoint pairwise_no_intersection (chords : list (list nat)) : Prop :=
  match chords with
  | [] => True
  | x :: xs => (forall y, In y xs -> ~has_intersection_chord x y) /\ pairwise_no_intersection xs
  end.

Fixpoint any_intersection_with (chord : list nat) (chords : list (list nat)) : bool :=
  match chords with
  | [] => false
  | y :: ys => has_intersection_chord_dec chord y || any_intersection_with chord ys
  end.

Fixpoint any_chord_intersects (chords : list (list nat)) : bool :=
  match chords with
  | [] => false
  | x :: xs => any_intersection_with x xs || any_chord_intersects xs
  end.

Definition hasChordIntersection_postcond_dec (N : nat) (chords : list (list nat)) (result : bool) : bool :=
  let sortedChords := map_normalize chords in
  negb (any_chord_intersects sortedChords) || negb result.
(* !benchmark @end postcond_aux *)

Definition hasChordIntersection_postcond (N : nat) (chords : (list (list nat))) (result : bool) (h_precond : hasChordIntersection_precond N chords) : Prop :=
  (* !benchmark @start postcond *)
  let sortedChords := map_normalize chords in
  (pairwise_no_intersection sortedChords -> result = false) /\
  (any_chord_intersects sortedChords = true -> result = true)
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem hasChordIntersection_postcond_satisfied (N : nat) (chords : (list (list nat))) (h_precond : hasChordIntersection_precond N chords) :
    hasChordIntersection_postcond N chords (hasChordIntersection N chords h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
