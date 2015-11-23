Require Export iris.cmra.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclUnit : excl A
  | ExclBot : excl A.
Arguments Excl {_} _.
Arguments ExclUnit {_}.
Arguments ExclBot {_}.
Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

(* Cofe *)
Inductive excl_equiv `{Equiv A} : Equiv (excl A) :=
  | Excl_equiv (x y : A) : x ≡ y → Excl x ≡ Excl y
  | ExclUnit_equiv : ExclUnit ≡ ExclUnit
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Inductive excl_dist `{Dist A} : Dist (excl A) :=
  | excl_dist_0 (x y : excl A) : x ={0}= y
  | Excl_dist (x y : A) n : x ={n}= y → Excl x ={n}= Excl y
  | ExclUnit_dist n : ExclUnit ={n}= ExclUnit
  | ExclBot_dist n : ExclBot ={n}= ExclBot.
Existing Instance excl_dist.
Program Definition excl_chain `{Cofe A}
    (c : chain (excl A)) (x : A) (H : maybe Excl (c 1) = Some x) : chain A :=
  {| chain_car n := match c n return _ with Excl y => y | _ => x end |}.
Next Obligation.
  intros A ???? c x ? n i ?; simpl; destruct (c 1) eqn:?; simplify_equality'.
  destruct (decide (i = 0)) as [->|].
  { by replace n with 0 by lia. }
  feed inversion (chain_cauchy c 1 i); auto with lia congruence.
  feed inversion (chain_cauchy c n i); simpl; auto with lia congruence.
Qed.
Instance excl_compl `{Cofe A} : Compl (excl A) := λ c,
  match Some_dec (maybe Excl (c 1)) with
  | inleft (exist x H) => Excl (compl (excl_chain c x H)) | inright _ => c 1
  end.
Local Instance excl_cofe `{Cofe A} : Cofe (excl A).
Proof.
  split.
  * intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
    intros Hxy; feed inversion (Hxy 1); subst; constructor; apply equiv_dist.
    by intros n; feed inversion (Hxy n).
  * intros n; split.
    + by intros [x| |]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
  * by inversion_clear 1; constructor; apply dist_S.
  * constructor.
  * intros c n; unfold compl, excl_compl.
    destruct (decide (n = 0)) as [->|]; [constructor|].
    destruct (Some_dec (maybe Excl (c 1))) as [[x Hx]|].
    { assert (c 1 = Excl x) by (by destruct (c 1); simplify_equality').
      assert (∃ y, c n = Excl y) as [y Hy].
      { feed inversion (chain_cauchy c 1 n); try congruence; eauto with lia. }
      rewrite Hy; constructor.
      by rewrite (conv_compl (excl_chain c x Hx) n); simpl; rewrite Hy. }
    feed inversion (chain_cauchy c 1 n); auto with lia; constructor.
    destruct (c 1); simplify_equality'.
Qed.

(* CMRA *)
Instance excl_valid {A} : Valid (excl A) := λ x,
  match x with Excl _ | ExclUnit => True | ExclBot => False end.
Instance excl_validN {A} : ValidN (excl A) := λ n x,
  match x with Excl _ | ExclUnit => True | ExclBot => n = 0 end.
Instance excl_empty {A} : Empty (excl A) := ExclUnit.
Instance excl_unit {A} : Unit (excl A) := λ _, ∅.
Instance excl_op {A} : Op (excl A) := λ x y,
  match x, y with
  | Excl x, ExclUnit | ExclUnit, Excl x => Excl x
  | ExclUnit, ExclUnit => ExclUnit
  | _, _=> ExclBot
  end.
Instance excl_minus {A} : Minus (excl A) := λ x y,
  match x, y with
  | _, ExclUnit => x
  | Excl _, Excl _ => ExclUnit
  | _, _ => ExclBot
  end.
Instance excl_cmra `{Cofe A} : CMRA (excl A).
Proof.
  split.
  * apply _.
  * by intros n []; destruct 1; constructor.
  * constructor.
  * by destruct 1 as [? []| | |]; intros ?.
  * by destruct 1; inversion_clear 1; constructor.
  * by intros [].
  * intros n [?| |]; simpl; auto with lia.
  * intros x; split; [by intros ? [|n]; destruct x|].
    by intros Hx; specialize (Hx 1); destruct x.
  * by intros [?| |] [?| |] [?| |]; constructor.
  * by intros [?| |] [?| |]; constructor.
  * by intros [?| |]; constructor.
  * constructor.
  * by intros n [?| |] [?| |]; exists ∅.
  * by intros n [?| |] [?| |].
  * by intros n [?| |] [?| |] [[?| |] Hz]; inversion_clear Hz; constructor.
Qed.
Instance excl_empty_ra `{Cofe A} : RAEmpty (excl A).
Proof. split. done. by intros []. Qed.
Instance excl_extend `{Cofe A} : CMRAExtend (excl A).
Proof.
  intros [|n] x y1 y2 ? Hx; [by exists (x,∅); destruct x|].
  by exists match y1, y2 with
    | Excl a1, Excl a2 => (Excl a1, Excl a2)
    | ExclBot, _ => (ExclBot, y2) | _, ExclBot => (y1, ExclBot)
    | ExclUnit, _ => (ExclUnit, x) | _, ExclUnit => (x, ExclUnit)
    end; destruct y1, y2; inversion_clear Hx; repeat constructor.
Qed.

(* Updates *)
Lemma excl_update {A} (x : A) y : ✓ y → Excl x ⇝ y.
Proof. by destruct y; intros ? [?| |]. Qed.

(* Functor *)
Definition exclRA (A : cofeT) : cmraT := CMRAT (excl A).
Instance excl_fmap : FMap excl := λ A B f x,
  match x with
  | Excl a => Excl (f a) | ExclUnit => ExclUnit | ExclBot => ExclBot
  end.
Instance excl_fmap_cmra_ne `{Dist A, Dist B} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap excl _ A B).
Proof. by intros f f' Hf; destruct 1; constructor; apply Hf. Qed.
Instance excl_fmap_cmra_monotone `{Cofe A, Cofe B} :
  (∀ n, Proper (dist n ==> dist n) f) → CMRAMonotone (fmap f : excl A → excl B).
Proof.
  split.
  * intros n x y [z Hy]; exists (f <$> z); rewrite Hy.
    by destruct x, z; constructor.
  * by intros n [a| |].
Qed.
Definition exclRA_map {A B : cofeT} (f : A -n> B) : exclRA A -n> exclRA B :=
  CofeMor (fmap f : exclRA A → exclRA B).
Lemma exclRA_map_ne A B n : Proper (dist n ==> dist n) (@exclRA_map A B).
Proof. by intros f f' Hf []; constructor; apply Hf. Qed.
