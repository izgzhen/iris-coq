From iris.algebra Require Export cmra.
From iris.algebra Require Import list.
From iris.base_logic Require Import base_logic.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(** Define an agreement construction such that Agree A is discrete when A is discrete.
    Notice that this construction is NOT complete.  The fullowing is due to Aleš:


Proposition: Ag(T) is not necessarily complete.
Proof.
  Let T be the set of binary streams (infinite sequences) with the usual
  ultrametric, measuring how far they agree.

  Let Aₙ be the set of all binary strings of length n. Thus for Aₙ to be a
  subset of T we have them continue as a stream of zeroes.

  Now Aₙ is a finite non-empty subset of T. Moreover {Aₙ} is a Cauchy sequence
  in the defined (Hausdorff) metric.

  However the limit (if it were to exist as an element of Ag(T)) would have to
  be the set of all binary streams, which is not exactly finite.

  Thus Ag(T) is not necessarily complete.
*)

Record agree (A : Type) : Type := Agree {
  agree_car : A;
  agree_with : list A;
}.
Arguments Agree {_} _ _.
Arguments agree_car {_} _.
Arguments agree_with {_} _.

(* Some theory about set-inclusion on lists and lists of which all elements are equal.
   TODO: Move this elsewhere. *)
Definition list_setincl `(R : relation A) (al bl : list A) :=
  ∀ a, a ∈ al → ∃ b, b ∈ bl ∧ R a b.
Definition list_setequiv `(R : relation A) (al bl : list A) :=
  list_setincl R al bl ∧ list_setincl R bl al.
(* list_agrees is carefully written such that, when applied to a
   singleton, it is convertible to True. This makes working with
   agreement much more pleasant. *)
Definition list_agrees `(R : relation A) (al : list A) :=
  match al with
  | [] => True
  | [a] => True
  | a :: al => ∀ b, b ∈ al → R a b
  end.

Lemma list_agrees_alt `(R : relation A) `{Equivalence _ R} al :
  list_agrees R al ↔ (∀ a b, a ∈ al → b ∈ al → R a b).
Proof.
  destruct al as [|a [|b al]].
  - split; last done. intros _ ? ? []%elem_of_nil.
  - split; last done. intros _ ? ? ->%elem_of_list_singleton ->%elem_of_list_singleton. done.
  - simpl. split.
    + intros Hl a' b' [->|Ha']%elem_of_cons.
      * intros [->|Hb']%elem_of_cons; first done. auto.
      * intros [->|Hb']%elem_of_cons; first by (symmetry; auto).
        trans a; last by auto. symmetry. auto.
    + intros Hl b' Hb'. apply Hl; set_solver.
Qed.

Section list_theory.
  Context `(R: relation A) `{Equivalence A R}.
  Collection Hyps := Type H.
  Local Set Default Proof Using "Hyps".

  Global Instance: PreOrder (list_setincl R).
  Proof.
    split.
    - intros al a Ha. set_solver.
    - intros al bl cl Hab Hbc a Ha. destruct (Hab _ Ha) as (b & Hb & Rab).
      destruct (Hbc _ Hb) as (c & Hc & Rbc). exists c. split; first done.
      by trans b.
  Qed.

  Global Instance: Equivalence (list_setequiv R).
  Proof.
    split.
    - by split.
    - intros ?? [??]. split; auto.
    - intros ??? [??] [??]. split; etrans; done.
  Qed.

  Global Instance list_setincl_subrel `(R' : relation A) :
    subrelation R R' → subrelation (list_setincl R) (list_setincl R').
  Proof using.
    intros HRR' al bl Hab. intros a Ha. destruct (Hab _ Ha) as (b & Hb & HR).
    exists b. split; first done. exact: HRR'.
  Qed.

  Global Instance list_setequiv_subrel `(R' : relation A) :
    subrelation R R' → subrelation (list_setequiv R) (list_setequiv R').
  Proof using. intros HRR' ?? [??]. split; exact: list_setincl_subrel. Qed.

  Global Instance list_setincl_perm : subrelation (≡ₚ) (list_setincl R).
  Proof.
    intros al bl Hab a Ha. exists a. split; last done.
    by rewrite -Hab.
  Qed.

  Global Instance list_setincl_app l :
    Proper (list_setincl R ==> list_setincl R) (app l).
  Proof.
    intros al bl Hab a [Ha|Ha]%elem_of_app.
    - exists a. split; last done. apply elem_of_app. by left.
    - destruct (Hab _ Ha) as (b & Hb & HR). exists b. split; last done.
      apply elem_of_app. by right.
  Qed.

  Global Instance list_setequiv_app l :
    Proper (list_setequiv R ==> list_setequiv R) (app l).
  Proof. intros al bl [??]. split; apply list_setincl_app; done. Qed.

  Global Instance: subrelation (≡ₚ) (flip (list_setincl R)).
  Proof. intros ???. apply list_setincl_perm. done. Qed.

  Global Instance list_agrees_setincl :
    Proper (flip (list_setincl R) ==> impl) (list_agrees R).
  Proof.
    move=> al bl /= Hab /list_agrees_alt Hal. apply (list_agrees_alt _) => a b Ha Hb.
    destruct (Hab _ Ha) as (a' & Ha' & HRa).
    destruct (Hab _ Hb) as (b' & Hb' & HRb).
    trans a'; first done. etrans; last done.
    eapply Hal; done.
  Qed.

  Global Instance list_agrees_setequiv :
    Proper (list_setequiv R ==> iff) (list_agrees R).
  Proof.
    intros ?? [??]. split; by apply: list_agrees_setincl.
  Qed.

  Lemma list_setincl_contains al bl :
    (∀ x, x ∈ al → x ∈ bl) → list_setincl R al bl.
  Proof. intros Hin a Ha. exists a. split; last done. naive_solver. Qed.

  Lemma list_setequiv_equiv al bl :
    (∀ x, x ∈ al ↔ x ∈ bl) → list_setequiv R al bl.
  Proof.
    intros Hin. split; apply list_setincl_contains; naive_solver.
  Qed.

  Lemma list_agrees_contains al bl :
    (∀ x, x ∈ bl → x ∈ al) →
    list_agrees R al → list_agrees R bl.
  Proof. intros ?. by eapply (list_agrees_setincl _),list_setincl_contains. Qed.

  Lemma list_agrees_equiv al bl :
    (∀ x, x ∈ bl ↔ x ∈ al) →
    list_agrees R al ↔ list_agrees R bl.
  Proof. intros ?. by eapply (list_agrees_setequiv _), list_setequiv_equiv. Qed.

  Lemma list_setincl_singleton a b :
    R a b → list_setincl R [a] [b].
  Proof.
    intros HR c ->%elem_of_list_singleton. exists b. split; last done.
    apply elem_of_list_singleton. done.
  Qed.

  Lemma list_setincl_singleton_rev a b :
    list_setincl R [a] [b] → R a b.
  Proof using.
    intros Hl. destruct (Hl a) as (? & ->%elem_of_list_singleton & HR); last done.
    by apply elem_of_list_singleton.
  Qed.

  Lemma list_setequiv_singleton a b :
    R a b → list_setequiv R [a] [b].
  Proof. intros ?. split; by apply list_setincl_singleton. Qed.

  Lemma list_agrees_iff_setincl al a :
    a ∈ al → list_agrees R al ↔ list_setincl R al [a].
  Proof.
    intros Hin. split.
    - move=>/list_agrees_alt Hl b Hb. exists a. split; first set_solver+. exact: Hl.
    - intros Hl. apply (list_agrees_alt _)=> b c Hb Hc.
      destruct (Hl _ Hb) as (? & ->%elem_of_list_singleton & ?).
      destruct (Hl _ Hc) as (? & ->%elem_of_list_singleton & ?).
      by trans a.
  Qed.

  Lemma list_setincl_singleton_in al a :
    a ∈ al → list_setincl R [a] al.
  Proof.
    intros Hin b ->%elem_of_list_singleton. exists a. split; done.
  Qed.

  Global Instance list_setincl_ext : subrelation (Forall2 R) (list_setincl R).
  Proof.
    move=>al bl. induction 1.
    - intros ? []%elem_of_nil.
    - intros a [->|Ha]%elem_of_cons.
      + eexists. split; first constructor. done.
      + destruct (IHForall2 _ Ha) as (b & ? & ?).
        exists b. split; first by constructor. done.
  Qed.

  Global Instance list_setequiv_ext : subrelation (Forall2 R) (list_setequiv R).
  Proof.
    move=>al bl ?. split; apply list_setincl_ext; done.
  Qed.

  Lemma list_agrees_subrel `(R' : relation A) `{Equivalence _ R'} :
    subrelation R R' → ∀ l, list_agrees R l → list_agrees R' l.
  Proof. move=> HR l /list_agrees_alt Hl. apply (list_agrees_alt _)=> a b Ha Hb. by apply HR, Hl. Qed.

  Section fmap.
    Context `(R' : relation B) (f : A → B) {Hf: Proper (R ==> R') f}.
    Collection Hyps := Type Hf.
    Local Set Default Proof Using "Hyps".

    Global Instance list_setincl_fmap :
      Proper (list_setincl R ==> list_setincl R') (fmap f).
    Proof using Hf.
      intros al bl Hab a' (a & -> & Ha)%elem_of_list_fmap.
      destruct (Hab _ Ha) as (b & Hb & HR). exists (f b).
      split; first eapply elem_of_list_fmap; eauto.
    Qed.

    Global Instance list_setequiv_fmap :
      Proper (list_setequiv R ==> list_setequiv R') (fmap f).
    Proof using Hf. intros ?? [??]. split; apply list_setincl_fmap; done. Qed.

    Lemma list_agrees_fmap `{Equivalence _ R'} al :
      list_agrees R al → list_agrees R' (f <$> al).
    Proof using Type*.
      move=> /list_agrees_alt Hl. apply (list_agrees_alt R') => a' b'.
      intros (a & -> & Ha)%elem_of_list_fmap (b & -> & Hb)%elem_of_list_fmap.
      apply Hf. exact: Hl.
    Qed.
  End fmap.
End list_theory.

Section agree.
Local Set Default Proof Using "Type".
Context {A : ofeT}.

Definition agree_list (x : agree A) := agree_car x :: agree_with x.

Instance agree_validN : ValidN (agree A) := λ n x,
  list_agrees (dist n) (agree_list x).
Instance agree_valid : Valid (agree A) := λ x,
  list_agrees (equiv) (agree_list x).

Instance agree_dist : Dist (agree A) := λ n x y,
  list_setequiv (dist n) (agree_list x) (agree_list y).
Instance agree_equiv : Equiv (agree A) := λ x y,
  ∀ n, list_setequiv (dist n) (agree_list x) (agree_list y).

Definition agree_dist_incl n (x y : agree A) :=
  list_setincl (dist n) (agree_list x) (agree_list y).

Definition agree_ofe_mixin : OfeMixin (agree A).
Proof.
  split.
  - intros x y; split; intros Hxy; done.
  - split; rewrite /dist /agree_dist; intros ? *.
    + reflexivity.
    + by symmetry.
    + intros. etrans; eassumption.
  - intros ???. apply list_setequiv_subrel=>??. apply dist_S.
Qed.
Canonical Structure agreeC := OfeT (agree A) agree_ofe_mixin.

Program Instance agree_op : Op (agree A) := λ x y,
  {| agree_car := agree_car x;
     agree_with := agree_with x ++ agree_car y :: agree_with y |}.
Instance agree_pcore : PCore (agree A) := Some.

Instance: Comm (≡) (@op (agree A) _).
Proof. intros x y n. apply: list_setequiv_equiv. set_solver. Qed.

Lemma agree_idemp (x : agree A) : x ⋅ x ≡ x.
Proof. intros n. apply: list_setequiv_equiv. set_solver. Qed.

Instance: ∀ n : nat, Proper (dist n ==> impl) (@validN (agree A) _ n).
Proof.
  intros n x y. rewrite /dist /validN /agree_dist /agree_validN.
  by intros ->.
Qed.
Instance: ∀ n : nat, Proper (equiv ==> iff) (@validN (agree A) _ n).
Proof.
  intros n ???. assert (x ≡{n}≡ y) as Hxy by by apply equiv_dist.
  split; rewrite Hxy; done.
Qed.

Instance: ∀ x : agree A, NonExpansive (op x).
Proof.
  intros x n y1 y2. rewrite /dist /agree_dist /agree_list /=.
  rewrite !app_comm_cons. apply: list_setequiv_app.
Qed.
Instance: NonExpansive2 (@op (agree A) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) op := ne_proper_2 _.
Instance: Assoc (≡) (@op (agree A) _).
Proof. intros x y z n. apply: list_setequiv_equiv. set_solver. Qed.

Lemma agree_included (x y : agree A) : x ≼ y ↔ y ≡ x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc agree_idemp.
Qed.
Lemma agree_op_inv_inclN n x1 x2 : ✓{n} (x1 ⋅ x2) → agree_dist_incl n x1 x2.
Proof.
  rewrite /validN /= => /list_agrees_alt Hv a /elem_of_cons Ha. exists (agree_car x2).
  split; first by constructor. eapply Hv.
  - simpl. destruct Ha as [->|Ha]; set_solver.
  - simpl. set_solver+.
Qed.

Lemma agree_op_invN n (x1 x2 : agree A) : ✓{n} (x1 ⋅ x2) → x1 ≡{n}≡ x2.
Proof.
  intros Hxy. split; apply agree_op_inv_inclN; first done. by rewrite comm.
Qed.

Lemma agree_valid_includedN n (x y : agree A) : ✓{n} y → x ≼{n} y → x ≡{n}≡ y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /agree_op_invN->; rewrite agree_idemp.
Qed.

Definition agree_cmra_mixin : CMRAMixin (agree A).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - move=>x. split.
    + move=>/list_agrees_alt Hx n. apply (list_agrees_alt _)=> a b Ha Hb.
      apply equiv_dist, Hx; done.
    + intros Hx. apply (list_agrees_alt _)=> a b Ha Hb.
      apply equiv_dist=>n. eapply (list_agrees_alt _); first (by apply Hx); done.
  - intros n x. apply (list_agrees_subrel _ _)=>??. apply dist_S.
  - intros x. apply agree_idemp.
  - intros ??? Hl. apply: list_agrees_contains Hl. set_solver.
  - intros n x y1 y2 Hval Hx; exists x, x; simpl; split.
    + by rewrite agree_idemp.
    + by move: Hval; rewrite Hx; move=> /agree_op_invN->; rewrite agree_idemp.
Qed.
Canonical Structure agreeR : cmraT := CMRAT (agree A) agree_cmra_mixin.

Global Instance agree_total : CMRATotal agreeR.
Proof. rewrite /CMRATotal; eauto. Qed.
Global Instance agree_persistent (x : agree A) : Persistent x.
Proof. by constructor. Qed.

Global Instance agree_discrete : Discrete A → CMRADiscrete agreeR.
Proof.
  intros HD. split.
  - intros x y Hxy n. eapply list_setequiv_subrel; last exact Hxy. clear -HD.
    intros x y ?. apply equiv_dist, HD. done.
  - rewrite /valid /cmra_valid /agree_valid /validN /cmra_validN /agree_validN /=.
    move=> x. apply (list_agrees_subrel _ _). clear -HD.
    intros x y. apply HD.
Qed.

Definition to_agree (x : A) : agree A :=
  {| agree_car := x; agree_with := [] |}.

Global Instance to_agree_ne : NonExpansive to_agree.
Proof.
  intros x1 x2 Hx; rewrite /= /dist /agree_dist /=.
  exact: list_setequiv_singleton.
Qed.
Global Instance to_agree_proper : Proper ((≡) ==> (≡)) to_agree := ne_proper _.

Global Instance to_agree_injN n : Inj (dist n) (dist n) (to_agree).
Proof. intros a b [Hxy%list_setincl_singleton_rev _]. done. Qed.
Global Instance to_agree_inj : Inj (≡) (≡) (to_agree).
Proof. intros a b ?. apply equiv_dist=>n. by apply to_agree_injN, equiv_dist. Qed.

Lemma to_agree_uninjN n (x : agree A) : ✓{n} x → ∃ y : A, to_agree y ≡{n}≡ x.
Proof.
  intros Hl. exists (agree_car x). rewrite /dist /agree_dist /=. split.
  - apply: list_setincl_singleton_in. set_solver+.
  - apply (list_agrees_iff_setincl _); first set_solver+. done.
Qed.

Lemma to_agree_uninj (x : agree A) : ✓ x → ∃ y : A, to_agree y ≡ x.
Proof.
  intros Hl. exists (agree_car x). rewrite /dist /agree_dist /=. split.
  - apply: list_setincl_singleton_in. set_solver+.
  - apply (list_agrees_iff_setincl _); first set_solver+.
    eapply list_agrees_subrel; last exact: Hl; [apply _..|].
    intros ???. by apply equiv_dist.
Qed.

Lemma to_agree_included (a b : A) : to_agree a ≼ to_agree b ↔ a ≡ b.
Proof.
  split.
  - intros (x & Heq). apply equiv_dist=>n. destruct (Heq n) as [_ Hincl].
    (* TODO: This could become a generic lemma about list_setincl. *)
    destruct (Hincl a) as (? & ->%elem_of_list_singleton & ?); first set_solver+.
    done.
  - by intros ->.
Qed.

Global Instance agree_cancelable (x : agree A) : Cancelable x.
Proof.
  intros n y z Hv Heq.
  destruct (to_agree_uninjN n x) as [x' EQx]; first by eapply cmra_validN_op_l.
  destruct (to_agree_uninjN n y) as [y' EQy]; first by eapply cmra_validN_op_r.
  destruct (to_agree_uninjN n z) as [z' EQz].
  { eapply (cmra_validN_op_r n x z). by rewrite -Heq. }
  assert (Hx'y' : x' ≡{n}≡ y').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQy. }
  assert (Hx'z' : x' ≡{n}≡ z').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQz -Heq. }
  by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Qed.

Lemma agree_op_inv (x1 x2 : agree A) : ✓ (x1 ⋅ x2) → x1 ≡ x2.
Proof.
  intros ?. apply equiv_dist=>n. by apply agree_op_invN, cmra_valid_validN.
Qed.
Lemma agree_op_inv' (a1 a2 : A) : ✓ (to_agree a1 ⋅ to_agree a2) → a1 ≡ a2.
Proof. by intros ?%agree_op_inv%(inj _). Qed.
Lemma agree_op_invL' `{!LeibnizEquiv A} (a1 a2 : A) :
  ✓ (to_agree a1 ⋅ to_agree a2) → a1 = a2.
Proof. by intros ?%agree_op_inv'%leibniz_equiv. Qed.

(** Internalized properties *)
Lemma agree_equivI {M} a b : to_agree a ≡ to_agree b ⊣⊢ (a ≡ b : uPred M).
Proof.
  uPred.unseal. do 2 split.
  - intros Hx. exact: to_agree_injN.
  - intros Hx. exact: to_agree_ne.
Qed.
Lemma agree_validI {M} x y : ✓ (x ⋅ y) ⊢ (x ≡ y : uPred M).
Proof. uPred.unseal; split=> r n _ ?; by apply: agree_op_invN. Qed.
End agree.

Instance: Params (@to_agree) 1.
Arguments agreeC : clear implicits.
Arguments agreeR : clear implicits.

Program Definition agree_map {A B} (f : A → B) (x : agree A) : agree B :=
  {| agree_car := f (agree_car x); agree_with := f <$> (agree_with x) |}.
Lemma agree_map_id {A} (x : agree A) : agree_map id x = x.
Proof. rewrite /agree_map /= list_fmap_id. by destruct x. Qed.
Lemma agree_map_compose {A B C} (f : A → B) (g : B → C) (x : agree A) :
  agree_map (g ∘ f) x = agree_map g (agree_map f x).
Proof. rewrite /agree_map /= list_fmap_compose. done. Qed.

Section agree_map.
  Context {A B : ofeT} (f : A → B) `{Hf: NonExpansive f}.
  Collection Hyps := Type Hf.
  Instance agree_map_ne : NonExpansive (agree_map f).
  Proof using Hyps.
    intros n x y Hxy.
    change (list_setequiv (dist n)(f <$> (agree_list x))(f <$> (agree_list y))).
    eapply list_setequiv_fmap; last exact Hxy. apply _.
  Qed.
  Instance agree_map_proper : Proper ((≡) ==> (≡)) (agree_map f) := ne_proper _.

  Lemma agree_map_ext (g : A → B) x :
    (∀ x, f x ≡ g x) → agree_map f x ≡ agree_map g x.
  Proof.
    intros Hfg n. apply: list_setequiv_ext.
    change (f <$> (agree_list x) ≡{n}≡ g <$> (agree_list x)).
    apply list_fmap_ext_ne=>y. by apply equiv_dist.
  Qed.

  Global Instance agree_map_morphism : CMRAMorphism (agree_map f).
  Proof using Hyps.
    split; first apply _.
    - intros n x. rewrite /cmra_validN /validN /= /agree_validN /= => ?.
      change (list_agrees (dist n) (f <$> agree_list x)).
      eapply (list_agrees_fmap _ _ _); done.
    - done.
    - intros x y n. apply: list_setequiv_equiv=>b.
      rewrite /agree_list /= !fmap_app. set_solver+.
  Qed.
End agree_map.

Definition agreeC_map {A B} (f : A -n> B) : agreeC A -n> agreeC B :=
  CofeMor (agree_map f : agreeC A → agreeC B).
Instance agreeC_map_ne A B : NonExpansive (@agreeC_map A B).
Proof.
  intros n f g Hfg x. apply: list_setequiv_ext.
  change (f <$> (agree_list x) ≡{n}≡ g <$> (agree_list x)).
  apply list_fmap_ext_ne. done.
Qed.

Program Definition agreeRF (F : cFunctor) : rFunctor := {|
  rFunctor_car A B := agreeR (cFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := agreeC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros ? A1 A2 B1 B2 n ???; simpl. by apply agreeC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x; simpl. rewrite -{2}(agree_map_id x).
  apply agree_map_ext=>y. by rewrite cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -agree_map_compose.
  apply agree_map_ext=>y; apply cFunctor_compose.
Qed.

Instance agreeRF_contractive F :
  cFunctorContractive F → rFunctorContractive (agreeRF F).
Proof.
  intros ? A1 A2 B1 B2 n ???; simpl.
  by apply agreeC_map_ne, cFunctor_contractive.
Qed.
