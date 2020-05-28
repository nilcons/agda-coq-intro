(*: Factorial in Coq *)
Require Import Coq.Arith.PeanoNat.

(*: Extract to Haskell *)
Require Extraction.
Extraction Language Haskell.

(******************************************************************************)
(*: Lists, append *)

Require Import Lists.List.
Import ListNotations.

(******************************************************************************)
(*: reverse list, fill the holes *)

(******************************************************************************)
(*: prove some lemmas about append *)

Lemma app_nil : forall (A : Type) (xs : list A), app xs [] = xs.
Proof.
Abort.

Lemma app_assoc : forall A (xs ys zs : list A), (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
Abort.

(*: Show how tactics are just constructing a proof term *)

(*: Try to prove that reverse is involution *)

Theorem rev_rev : forall A (xs : list A), reverse (reverse xs) = xs.
Abort.


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
