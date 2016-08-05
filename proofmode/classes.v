From iris.algebra Require Export upred.
Import uPred.

Section classes.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Class FromAssumption (p : bool) (P Q : uPred M) := from_assumption : □?p P ⊢ Q.
Global Arguments from_assumption _ _ _ {_}.

Class IntoPure (P : uPred M) (φ : Prop) := into_pure : P ⊢ ■ φ.
Global Arguments into_pure : clear implicits.

Class FromPure (P : uPred M) (φ : Prop) := from_pure : φ → True ⊢ P.
Global Arguments from_pure : clear implicits.

Class IntoPersistentP (P Q : uPred M) := into_persistentP : P ⊢ □ Q.
Global Arguments into_persistentP : clear implicits.

Class IntoLater (P Q : uPred M) := into_later : P ⊢ ▷ Q.
Global Arguments into_later _ _ {_}.

Class FromLater (P Q : uPred M) := from_later : ▷ Q ⊢ P.
Global Arguments from_later _ _ {_}.

Class IntoWand (R P Q : uPred M) := into_wand : R ⊢ P -★ Q.
Global Arguments into_wand : clear implicits.

Class FromAnd (P Q1 Q2 : uPred M) := from_and : Q1 ∧ Q2 ⊢ P.
Global Arguments from_and : clear implicits.

Class FromSep (P Q1 Q2 : uPred M) := from_sep : Q1 ★ Q2 ⊢ P.
Global Arguments from_sep : clear implicits.

Class IntoSep (p: bool) (P Q1 Q2 : uPred M) := into_sep : □?p P ⊢ □?p (Q1 ★ Q2).
Global Arguments into_sep : clear implicits.

Class IntoOp {A : cmraT} (a b1 b2 : A) := into_op : a ≡ b1 ⋅ b2.
Global Arguments into_op {_} _ _ _ {_}.

Class Frame (R P Q : uPred M) := frame : R ★ Q ⊢ P.
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

Class IntoNowTrue (P Q : uPred M) := into_now_True : P ⊢ ◇ Q.
Global Arguments into_now_True : clear implicits.

Class IsNowTrue (Q : uPred M) := is_now_True : ◇ Q ⊢ Q.
Global Arguments is_now_True : clear implicits.

Class FromVs (P Q : uPred M) := from_vs : (|=r=> Q) ⊢ P.
Global Arguments from_vs : clear implicits.

Class ElimVs (P P' : uPred M) (Q Q' : uPred M) :=
  elim_vs : P ★ (P' -★ Q') ⊢ Q.
Arguments elim_vs _ _ _ _ {_}.
End classes.
