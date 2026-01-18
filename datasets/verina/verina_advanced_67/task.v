(* !benchmark @start import type=task *)
Require Import String.
(* !benchmark @end import *)

(* !benchmark @start import type=solution *)
Require Import Ascii String List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
(* !benchmark @end import *)

(* !benchmark @start task_aux *)
(* task-level type definitions: Record, Inductive, etc. - translate from Lean task_aux *)
(* !benchmark @end task_aux *)

(* !benchmark @start solution_aux *)
(* complete helper definitions with Fixpoint/Definition keywords *)
(* !benchmark @end solution_aux *)

(* !benchmark @start precond_aux *)
(* precondition helpers including _dec version, complete definitions *)
Definition runLengthEncode_precond_dec (s : string) : bool := true.
(* !benchmark @end precond_aux *)

Definition runLengthEncode_precond (s : string) : Prop :=
  (* !benchmark @start precond *)
  True
  (* !benchmark @end precond *).

(* !benchmark @start code_aux *)
(* Helper to convert string to list of ascii chars *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

(* The recursive encoding function *)
Fixpoint encodeAux (acc : list (ascii * nat)) (rest : list ascii) : list (ascii * nat) :=
  match rest with
  | [] => rev acc
  | h :: t =>
    match acc with
    | (ch, count) :: accTail =>
      if ascii_dec ch h then
        encodeAux ((ch, (count + 1)%nat) :: accTail) t
      else
        encodeAux ((h, 1%nat) :: (ch, count) :: accTail) t
    | [] =>
      encodeAux [(h, 1%nat)] t
    end
  end.
(* !benchmark @end code_aux *)

Definition runLengthEncode (s : string) (h_precond : runLengthEncode_precond s) : list (ascii * nat) :=
  (* !benchmark @start code *)
  let chars := string_to_list s in
  encodeAux [] chars
  (* !benchmark @end code *).

(* !benchmark @start postcond_aux *)
(* Helper to decode RLE back to string *)
Fixpoint decodeRLE (lst : list (ascii * nat)) : string :=
  match lst with
  | [] => EmptyString
  | (ch, cnt) :: tail =>
    let repeated := fold_right String EmptyString (repeat ch cnt) in
    append repeated (decodeRLE tail)
  end.

(* Check if all pairs have positive count *)
Fixpoint all_positive_counts (lst : list (ascii * nat)) : Prop :=
  match lst with
  | [] => True
  | (_, cnt) :: tail => (cnt > 0)%nat /\ all_positive_counts tail
  end.

Fixpoint all_positive_counts_dec (lst : list (ascii * nat)) : bool :=
  match lst with
  | [] => true
  | (_, cnt) :: tail => (Nat.ltb 0 cnt && all_positive_counts_dec tail)%bool
  end.

(* Check if consecutive pairs have different characters *)
Fixpoint consecutive_different (lst : list (ascii * nat)) : Prop :=
  match lst with
  | [] => True
  | [_] => True
  | (ch1, _) :: ((ch2, _) :: _) as tail =>
    ch1 <> ch2 /\ consecutive_different tail
  end.

Fixpoint consecutive_different_dec (lst : list (ascii * nat)) : bool :=
  match lst with
  | [] => true
  | [_] => true
  | (ch1, _) :: ((ch2, _) :: _) as tail =>
    (negb (if ascii_dec ch1 ch2 then true else false) && consecutive_different_dec tail)%bool
  end.

Definition runLengthEncode_postcond_dec (s : string) (result : list (ascii * nat)) : bool :=
  (all_positive_counts_dec result && consecutive_different_dec result && String.eqb (decodeRLE result) s)%bool.
(* !benchmark @end postcond_aux *)

Definition runLengthEncode_postcond (s : string) (result : list (ascii * nat)) (h_precond : runLengthEncode_precond s) : Prop :=
  (* !benchmark @start postcond *)
  all_positive_counts result /\ consecutive_different result /\ decodeRLE result = s
  (* !benchmark @end postcond *).

(* !benchmark @start proof_aux *)

(* !benchmark @end proof_aux *)

Theorem runLengthEncode_postcond_satisfied (s : string) (h_precond : runLengthEncode_precond s) :
    runLengthEncode_postcond s (runLengthEncode s h_precond) h_precond.
Proof.
  (* !benchmark @start proof *)
  admit.
  (* !benchmark @end proof *)
Admitted.
