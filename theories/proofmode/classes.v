From iris.base_logic Require Export base_logic.
Set Default Proof Using "Type".
Import uPred.

Section classes.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Class FromAssumption (p : bool) (P Q : uPred M) := from_assumption : □?p P ⊢ Q.
Global Arguments from_assumption _ _ _ {_}.

Class IntoPure (P : uPred M) (φ : Prop) := into_pure : P ⊢ ⌜φ⌝.
Global Arguments into_pure : clear implicits.

Class FromPure (P : uPred M) (φ : Prop) := from_pure : ⌜φ⌝ ⊢ P.
Global Arguments from_pure : clear implicits.

Class IntoPersistentP (P Q : uPred M) := into_persistentP : P ⊢ □ Q.
Global Arguments into_persistentP : clear implicits.

Class IntoLaterN (n : nat) (P Q : uPred M) := into_laterN : P ⊢ ▷^n Q.
Global Arguments into_laterN _ _ _ {_}.

Class FromLaterN (n : nat) (P Q : uPred M) := from_laterN : ▷^n Q ⊢ P.
Global Arguments from_laterN _ _ _ {_}.

Class IntoWand (R P Q : uPred M) := into_wand : R ⊢ P -∗ Q.
Global Arguments into_wand : clear implicits.

Class FromAnd (P Q1 Q2 : uPred M) := from_and : Q1 ∧ Q2 ⊢ P.
Global Arguments from_and : clear implicits.

Class FromSep (P Q1 Q2 : uPred M) := from_sep : Q1 ∗ Q2 ⊢ P.
Global Arguments from_sep : clear implicits.

Class IntoAnd (p : bool) (P Q1 Q2 : uPred M) :=
  into_and : P ⊢ if p then Q1 ∧ Q2 else Q1 ∗ Q2.
Global Arguments into_and : clear implicits.

Lemma mk_into_and_sep p P Q1 Q2 : (P ⊢ Q1 ∗ Q2) → IntoAnd p P Q1 Q2.
Proof. rewrite /IntoAnd=>->. destruct p; auto using sep_and. Qed.

Class FromOp {A : cmraT} (a b1 b2 : A) := from_op : b1 ⋅ b2 ≡ a.
Global Arguments from_op {_} _ _ _ {_}.

Class IntoOp {A : cmraT} (a b1 b2 : A) := into_op : a ≡ b1 ⋅ b2.
Global Arguments into_op {_} _ _ _ {_}.

Class Frame (R P Q : uPred M) := frame : R ∗ Q ⊢ P.
Global Arguments frame : clear implicits.

Class FromOr (P Q1 Q2 : uPred M) := from_or : Q1 ∨ Q2 ⊢ P.
Global Arguments from_or : clear implicits.

Class IntoOr P Q1 Q2 := into_or : P ⊢ Q1 ∨ Q2.
Global Arguments into_or : clear implicits.

Class FromExist {A} (P : uPred M) (Φ : A → uPred M) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Global Arguments from_exist {_} _ _ {_}.

Class IntoExist {A} (P : uPred M) (Φ : A → uPred M) :=
  into_exist : P ⊢ ∃ x, Φ x.
Global Arguments into_exist {_} _ _ {_}.

Class IntoModal (P Q : uPred M) := into_modal : P ⊢ Q.
Global Arguments into_modal : clear implicits.

Class ElimModal (P P' : uPred M) (Q Q' : uPred M) :=
  elim_modal : P ∗ (P' -∗ Q') ⊢ Q.
Global Arguments elim_modal _ _ _ _ {_}.

Lemma elim_modal_dummy P Q : ElimModal P P Q Q.
Proof. by rewrite /ElimModal wand_elim_r. Qed.

Class IsExcept0 (Q : uPred M) := is_except_0 : ◇ Q ⊢ Q.
Global Arguments is_except_0 : clear implicits.
End classes.
