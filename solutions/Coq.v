(*: Factorial in Coq *)
Require Import Coq.Arith.PeanoNat.

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

Check (fact 5).
Compute fact 5.

(*: Extract to Haskell *)
Require Extraction.
Extraction Language Haskell.

Extraction fact.

(******************************************************************************)
(*: Lists, append *)

Require Import Lists.List.
Import ListNotations.

Fixpoint append {A} (xs ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: append xs' ys
  end.

Compute append [1; 2; 3] [4; 5].

Extraction append.

(******************************************************************************)
(*: reverse list, fill the holes *)

Definition reverse {A} : list A -> list A.
  refine (
      fix rev (xs : list A) :=
        match xs with
        | [] => _
        | x :: xs' => (* append (rev _) [_] *) rev _ ++ [_]
        end
    ); auto.
Defined.

Compute reverse [1; 2; 3; 4].

Locate "_ ++ _".
Print app.

Extraction reverse.
Extraction list.

Extract Inductive list => "List" [ "[]" "(:)" ].
Recursive Extraction reverse.

(******************************************************************************)
(*: prove some lemmas about append *)

Lemma app_nil : forall (A : Type) (xs : list A), app xs [] = xs.
Proof.
  intros.
  induction xs.
  - easy.
  - simpl.
    rewrite IHxs.
    easy.
Qed.

Lemma app_assoc : forall A (xs ys zs : list A), (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  intros.
  induction xs; simpl.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

(*: Show how tactics are just constructing a proof term *)

Definition append' {A} (xs ys : list A) : list A.
  induction xs.
  - exact ys.
  - apply cons.
    + assumption.
    + apply IHxs.
Defined.

Print append'.
Compute append' [1; 2; 3] [4; 5; 6].

(*: Try to prove that reverse is involution *)

Theorem rev_rev : forall A (xs : list A), reverse (reverse xs) = xs.
  intros.
  induction xs; simpl.
  - easy.
  -
Abort.

Lemma rev_append : forall A (xs ys : list A), reverse (xs ++ ys) = reverse ys ++ reverse xs.
  intros.
  induction xs; simpl.
  - rewrite app_nil; easy.
  - rewrite IHxs. rewrite app_assoc. easy.
Qed.

Theorem rev_rev : forall A (xs : list A), reverse (reverse xs) = xs.
  intros.
  induction xs; simpl.
  - easy.
  - rewrite rev_append. simpl. rewrite IHxs. easy.
Qed.


(******************************************************************************)
(*
  Where Coq is used?

  Georges Gonthier, Four Color Theorem, Odd Order Theorem.

  Certified C compiler (for x86, x86_64, ARM, PowerPC)
  http://compcert.inria.fr/

  Verified Everything
  https://deepspec.org/main

  Awesome Coq
  https://github.com/uhub/awesome-coq
*)
