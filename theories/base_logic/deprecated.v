(*
FIXME

From iris.base_logic Require Import primitive.
Set Default Proof Using "Type".

(* Deprecated 2016-11-22. Use ⌜φ⌝ instead. *)
Notation "■ φ" := (uPred_pure φ%C%type)
    (at level 20, right associativity, only parsing) : uPred_scope.

(* Deprecated 2016-11-22. Use ⌜x = y⌝ instead. *)
Notation "x = y" := (uPred_pure (x%C%type = y%C%type)) (only parsing) : uPred_scope.

(* Deprecated 2016-11-22. Use ⌜x ⊥ y ⌝ instead. *)
Notation "x ⊥ y" := (uPred_pure (x%C%type ⊥ y%C%type)) (only parsing) : uPred_scope.
*)
