From iris.algebra Require Export cmra.
From iris.algebra Require Import updates.
From stdpp Require Import finite.
Set Default Proof Using "Type".

Definition iprod_insert `{EqDecision A} {B : A → ofeT}
    (x : A) (y : B x) (f : iprod B) : iprod B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Instance: Params (@iprod_insert) 5.

Definition iprod_singleton `{Finite A} {B : A → ucmraT} 
  (x : A) (y : B x) : iprod B := iprod_insert x y ε.
Instance: Params (@iprod_singleton) 5.

Section ofe.
  Context `{Heqdec : EqDecision A} {B : A → ofeT}.
  Implicit Types x : A.
  Implicit Types f g : iprod B.

  (** Properties of iprod_insert. *)
  Global Instance iprod_insert_ne x :
    NonExpansive2 (iprod_insert (B:=B) x).
  Proof.
    intros n y1 y2 ? f1 f2 ? x'; rewrite /iprod_insert.
    by destruct (decide _) as [[]|].
  Qed.
  Global Instance iprod_insert_proper x :
    Proper ((≡) ==> (≡) ==> (≡)) (iprod_insert x) := ne_proper_2 _.

  Lemma iprod_lookup_insert f x y : (iprod_insert x y f) x = y.
  Proof.
    rewrite /iprod_insert; destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
  Lemma iprod_lookup_insert_ne f x x' y :
    x ≠ x' → (iprod_insert x y f) x' = f x'.
  Proof. by rewrite /iprod_insert; destruct (decide _). Qed.

  Global Instance iprod_insert_discrete f x y :
    Discrete f → Discrete y → Discrete (iprod_insert x y f).
  Proof.
    intros ?? g Heq x'; destruct (decide (x = x')) as [->|].
    - rewrite iprod_lookup_insert.
      apply: discrete. by rewrite -(Heq x') iprod_lookup_insert.
    - rewrite iprod_lookup_insert_ne //.
      apply: discrete. by rewrite -(Heq x') iprod_lookup_insert_ne.
  Qed.
End ofe.

Section cmra.
  Context `{Finite A} {B : A → ucmraT}.
  Implicit Types x : A.
  Implicit Types f g : iprod B.

  Global Instance iprod_singleton_ne x :
    NonExpansive (iprod_singleton x : B x → _).
  Proof. intros n y1 y2 ?; apply iprod_insert_ne. done. by apply equiv_dist. Qed.
  Global Instance iprod_singleton_proper x :
    Proper ((≡) ==> (≡)) (iprod_singleton x) := ne_proper _.

  Lemma iprod_lookup_singleton x (y : B x) : (iprod_singleton x y) x = y.
  Proof. by rewrite /iprod_singleton iprod_lookup_insert. Qed.
  Lemma iprod_lookup_singleton_ne x x' (y : B x) :
    x ≠ x' → (iprod_singleton x y) x' = ε.
  Proof. intros; by rewrite /iprod_singleton iprod_lookup_insert_ne. Qed.

  Global Instance iprod_singleton_discrete x (y : B x) :
    (∀ i, Discrete (ε : B i)) →  Discrete y → Discrete (iprod_singleton x y).
  Proof. apply _. Qed.

  Lemma iprod_singleton_validN n x (y : B x) : ✓{n} iprod_singleton x y ↔ ✓{n} y.
  Proof.
    split; [by move=>/(_ x); rewrite iprod_lookup_singleton|].
    move=>Hx x'; destruct (decide (x = x')) as [->|];
      rewrite ?iprod_lookup_singleton ?iprod_lookup_singleton_ne //.
    by apply ucmra_unit_validN.
  Qed.

  Lemma iprod_core_singleton x (y : B x) :
    core (iprod_singleton x y) ≡ iprod_singleton x (core y).
  Proof.
    move=>x'; destruct (decide (x = x')) as [->|];
      by rewrite iprod_lookup_core ?iprod_lookup_singleton
      ?iprod_lookup_singleton_ne // (core_id_core ∅).
  Qed.

  Global Instance iprod_singleton_core_id x (y : B x) :
    CoreId y → CoreId (iprod_singleton x y).
  Proof. by rewrite !core_id_total iprod_core_singleton=> ->. Qed.

  Lemma iprod_op_singleton (x : A) (y1 y2 : B x) :
    iprod_singleton x y1 ⋅ iprod_singleton x y2 ≡ iprod_singleton x (y1 ⋅ y2).
  Proof.
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite iprod_lookup_op !iprod_lookup_singleton.
    - by rewrite iprod_lookup_op !iprod_lookup_singleton_ne // left_id.
  Qed.

  Lemma iprod_insert_updateP x (P : B x → Prop) (Q : iprod B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (iprod_insert x y2 g)) →
    iprod_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite iprod_lookup_op iprod_lookup_insert. }
    exists (iprod_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite iprod_lookup_op ?iprod_lookup_insert //; [].
    move: (Hg x'). by rewrite iprod_lookup_op !iprod_lookup_insert_ne.
  Qed.

  Lemma iprod_insert_updateP' x (P : B x → Prop) g y1 :
    y1 ~~>: P →
    iprod_insert x y1 g ~~>: λ g', ∃ y2, g' = iprod_insert x y2 g ∧ P y2.
  Proof. eauto using iprod_insert_updateP. Qed.
  Lemma iprod_insert_update g x y1 y2 :
    y1 ~~> y2 → iprod_insert x y1 g ~~> iprod_insert x y2 g.
  Proof.
    rewrite !cmra_update_updateP; eauto using iprod_insert_updateP with subst.
  Qed.

  Lemma iprod_singleton_updateP x (P : B x → Prop) (Q : iprod B → Prop) y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (iprod_singleton x y2)) →
    iprod_singleton x y1 ~~>: Q.
  Proof. rewrite /iprod_singleton; eauto using iprod_insert_updateP. Qed.
  Lemma iprod_singleton_updateP' x (P : B x → Prop) y1 :
    y1 ~~>: P →
    iprod_singleton x y1 ~~>: λ g, ∃ y2, g = iprod_singleton x y2 ∧ P y2.
  Proof. eauto using iprod_singleton_updateP. Qed.
  Lemma iprod_singleton_update x (y1 y2 : B x) :
    y1 ~~> y2 → iprod_singleton x y1 ~~> iprod_singleton x y2.
  Proof. eauto using iprod_insert_update. Qed.

  Lemma iprod_singleton_updateP_empty x (P : B x → Prop) (Q : iprod B → Prop) :
    ε ~~>: P → (∀ y2, P y2 → Q (iprod_singleton x y2)) → ε ~~>: Q.
  Proof.
    intros Hx HQ; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hx n (Some (gf x))) as (y2&?&?); first apply Hg.
    exists (iprod_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite iprod_lookup_op iprod_lookup_singleton.
    - rewrite iprod_lookup_op iprod_lookup_singleton_ne //. apply Hg.
  Qed.
  Lemma iprod_singleton_updateP_empty' x (P : B x → Prop) :
    ε ~~>: P → ε ~~>: λ g, ∃ y2, g = iprod_singleton x y2 ∧ P y2.
  Proof. eauto using iprod_singleton_updateP_empty. Qed.
  Lemma iprod_singleton_update_empty x (y : B x) :
    ε ~~> y → ε ~~> iprod_singleton x y.
  Proof.
    rewrite !cmra_update_updateP;
      eauto using iprod_singleton_updateP_empty with subst.
  Qed.
End cmra.
