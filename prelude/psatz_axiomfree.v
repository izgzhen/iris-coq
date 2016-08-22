(** This file is a hack that lets us use Psatz without importing all sorts of
    axioms about real numbers.  It has been created by copying the file
    Psatz.v from the Coq distribution, removing everything defined after the lia
    tactic, and removing the two lines importing RMicromega and Rdefinitions.
    The original license header follows. *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

From Coq Require Import ZMicromega.
From Coq Require Import QMicromega.
From Coq Require Import QArith.
From Coq Require Import ZArith.
From Coq Require Import RingMicromega.
From Coq Require Import VarMap.
From Coq Require Tauto.
Declare ML Module "micromega_plugin".

Ltac preprocess := 
    zify ; unfold Z.succ in * ; unfold Z.pred in *.

Ltac lia :=
  preprocess;
  xlia ;
  abstract (
  intros __wit __varmap __ff ;
    change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ;
      apply (ZTautoChecker_sound __ff __wit); vm_cast_no_check (eq_refl true)).
