From algebra Require Export cmra.
From algebra Require Import cmra_big_op.

(** * Simple solver for validity and inclusion by reflection *)
Module ra_reflection. Section ra_reflection.
  Context `{CMRAUnit A}.

  Inductive expr :=
    | EVar : nat → expr
    | EEmpty : expr
    | EOp : expr → expr → expr.
  Fixpoint eval (Σ : list A) (e : expr) : A :=
    match e with
    | EVar n => from_option ∅ (Σ !! n)
    | EEmpty => ∅
    | EOp e1 e2 => eval Σ e1 ⋅ eval Σ e2
    end.
  Fixpoint flatten (e : expr) : list nat :=
    match e with
    | EVar n => [n]
    | EEmpty => []
    | EOp e1 e2 => flatten e1 ++ flatten e2
    end.
  Lemma eval_flatten Σ e :
    eval Σ e ≡ big_op ((λ n, from_option ∅ (Σ !! n)) <$> flatten e).
  Proof.
    by induction e as [| |e1 IH1 e2 IH2];
      rewrite /= ?right_id ?fmap_app ?big_op_app ?IH1 ?IH2.
  Qed.
  Lemma flatten_correct Σ e1 e2 :
    flatten e1 `contains` flatten e2 → eval Σ e1 ≼ eval Σ e2.
  Proof.
    by intros He; rewrite !eval_flatten; apply big_op_contains; rewrite ->He.
  Qed.

  Class Quote (Σ1 Σ2 : list A) (l : A) (e : expr) := {}.
  Global Instance quote_empty: Quote E1 E1 ∅ EEmpty.
  Global Instance quote_var Σ1 Σ2 e i:
    rlist.QuoteLookup Σ1 Σ2 e i → Quote Σ1 Σ2 e (EVar i) | 1000.
  Global Instance quote_app Σ1 Σ2 Σ3 x1 x2 e1 e2 :
    Quote Σ1 Σ2 x1 e1 → Quote Σ2 Σ3 x2 e2 → Quote Σ1 Σ3 (x1 ⋅ x2) (EOp e1 e2).
  End ra_reflection.

  Ltac quote :=
    match goal with
    | |- @included _ _ _ ?x ?y =>
      lazymatch type of (_ : Quote [] _ x _) with Quote _ ?Σ2 _ ?e1 =>
      lazymatch type of (_ : Quote Σ2 _ y _) with Quote _ ?Σ3 _ ?e2 =>
        change (eval Σ3 e1 ≼ eval Σ3 e2)
      end end
    end.
End ra_reflection.

Ltac solve_included :=
  ra_reflection.quote;
  apply ra_reflection.flatten_correct, (bool_decide_unpack _);
  vm_compute; apply I.

Ltac solve_validN :=
  match goal with
  | H : ✓{?n} ?y |- ✓{?n'} ?x =>
     let Hn := fresh in let Hx := fresh in
     assert (n' ≤ n) as Hn by omega;
     assert (x ≼ y) as Hx by solve_included;
     eapply cmra_validN_le, Hn; eapply cmra_validN_included, Hx; apply H
  end.
