(** This module implements the core theory of complete bisected ultrametric
    spaces. It starts with their definition and simple properties. In the last part
    the standard constructions are defined, the same as in CSetoids.

    The distance function is really defined as picking out equivalence classes
    directly, instead of the usual definition with a map into reals. The approaches
    are equivalent for bisected metric spaces. *)

Require Export CSetoid.
Require Import Omega.
Require Import Min Max.

Open Scope nat_scope.

Generalizable Variables T U V W.

(** ** 1-Bounded bisected Ultra Metric type
    d_n(x,y) <-> |x - y| <= 1/2^n *)

(** Metric on the [type] M with requirements. Note that this only covers bisected metric spaces.
    To fully follow the unbundled style, we'd have to factor out "dist" - but things already work
    pretty well this way. *)
Class metric (T : Type) {eqT : Setoid T} :=
  { dist         :  nat -> T -> T -> Prop;
    dist_morph n :> Proper (equiv ==> equiv ==> iff) (dist n);
    dist_refl    :  forall x y, (forall n, dist n x y) <-> x == y;
    dist_sym   n :> Symmetric (dist n);
    dist_trans n :> Transitive (dist n);
    dist_mono    :  forall n x y, dist (S n) x y -> dist n x y;
    dist_bound   :  forall x y, dist 0 x y}.

Notation "'mkMetr' D" := (Build_metric _ _ D _ _ _ _ _ _) (at level 10).

Record Mtyp :=
  { mtyp  :> eqType;
    mmetr : metric mtyp}.
Instance mtyp_proj_metr {M : Mtyp} : metric M := mmetr M.
Definition mfromType (T : Type) `{mT : metric T} := Build_Mtyp (fromType T) _.

(* And now it gets annoying that we are not fully unbundled... *)
Global Instance metric_dist_equiv (T: Type) `{mT: metric T} n: Equivalence (dist n).
Proof.
  split.
  - intros x. eapply dist_refl. reflexivity.
  - now eapply dist_sym.
  - now eapply dist_trans.
Qed.

Section DistProps.
  Context `{mT : metric T}.

  Lemma mono_dist x y m n (HLe : m <= n) : dist n x y -> dist m x y.
  Proof.
    induction HLe; [tauto |].
    intros HS; apply IHHLe, dist_mono; assumption.
  Qed.

  (** The spaces are ultrametric spaces. *)
  Lemma tai_dist x y z n m (HL : dist n x y) (HR : dist m y z) :
    dist (min m n) x z.
  Proof.
    etransitivity; eapply mono_dist; try eassumption; eauto using le_min_r, le_min_l.
  Qed.

  Global Instance Reflexive_dist n : Reflexive (dist n).
  Proof. intros x; revert n; rewrite dist_refl; reflexivity. Qed.

End DistProps.

Notation "x '=' n '=' y" := (dist n x y).

Instance dist_iff `{metric T} n : Proper (dist n ==> dist n ==> iff) (dist n).
Proof.
  intros x y EQxy u v EQuv; split; intros EQ; [symmetry in EQxy, EQuv |];
  rewrite EQxy, EQuv; assumption.
Qed.

Existing Class le.

Existing Instance le_plus_trans.
Instance le_plus_trans' n m p {HLe : n <= p} : n <= m + p.
Proof.
  rewrite plus_comm; apply _.
Qed.
Existing Instance le_S.
Existing Instance le_n.
Instance max_le_tr_l n m p {HLe : n <= m} : n <= max m p.
Proof.
  rewrite HLe; apply le_max_l.
Qed.
Instance max_le_tr_r n m p {HLe : n <= p} : n <= max m p.
Proof.
  rewrite HLe; apply le_max_r.
Qed.

Instance mono_proper `{metric T} m n {HLe : n <= m} :
  Proper (dist m ==> dist m ==> iff) (dist n).
Proof.
  intros m1 m2 EQm m3 m4 EQm'.
  eapply mono_dist in EQm; [| eassumption].
  eapply mono_dist in EQm'; [| eassumption].
  rewrite EQm, EQm'; reflexivity.
Qed.

(** Cauchy chains of elements of a metric spaces. This is a very strong form of
convergence, since we require than all elements after the n-th are closer than 2⁻ⁿ.*)
Definition chain (T : Type) := nat -> T.
Class cchain `{mT : metric T} (σ : chain T): Prop :=
  chain_cauchy : forall n i j {HLei : n <= i} {HLej : n <= j}, (σ i) = n = (σ j).

Arguments cchain [T eqT mT] σ.
Arguments chain_cauchy [T eqT mT] _ _ n i j {HLei HLej}.

Section Chains.
  Context `(σ : chain T) `{σc : cchain _ σ}.

  (** n-th tail of the sequence *)
  Definition cutn (n : nat) : chain T := fun i => σ (n + i).
  Global Instance cutn_cauchy (n : nat) : cchain (cutn n).
  Proof.
    intros k i j HLei HLej.
    unfold cutn.
    apply mono_dist with (n + k); [apply _ |].
    apply σc; now apply plus_le_compat_l.
  Qed.

  (** Constant chains are chains. *)
  Global Instance const_chain m : cchain (fun _ => m).
  Proof. unfold cchain; reflexivity. Qed.

  (** Chain [c] converges to [x].
      NOTE: Interesting that here you require an existence of [m] and not that every element after n-th is closer than 2⁻ⁿ. *)
  Definition mconverge (m : T) :=
    forall n, exists k, forall i {HLe : k <= i}, m = n = (σ i).

End Chains.

(* Again, this is not fully unbundled - "compl" is a computational component *)
Class cmetric T `{mT : metric T} :=
  { compl       : forall σ {σc : cchain σ}, T;
    conv_cauchy : forall σ {σc : cchain σ}, mconverge σ (compl σ)}.

Notation "'mkCMetr' C" := (Build_cmetric _ _ _ C _) (at level 10).

(*(** Completion assigns to each Cauchy chain an element of M, such that the chain
converges to that element, i.e. it assigns it an actual limit. *)
Class Completion M `{mM : metric M} := mcompl : forall (σ : chain M) (σc : cchain σ), M.
Arguments mcompl {M e eqM D mM Completion} σ {σc}.

Class cmetric M `{mM : metric M} {cM : Completion M} :=
  conv_cauchy : forall σ {σc : cchain σ}, mconverge σ (mcompl σ).
*)

Record cmtyp :=
  { cmm  :> Mtyp;
    iscm :  cmetric cmm}.
Instance cmtyp_cmetric {M : cmtyp} : cmetric M | 0 := iscm M.
Definition cmfromType (T : Type) `{cT : cmetric T} := Build_cmtyp (mfromType T) _.

Section ChainCompl.
  Context `{cT : cmetric T} (σ ρ : chain T) {σc : cchain σ} {ρc : cchain ρ}.

  Lemma umet_complete_extn n (HEq : forall i, σ i = n = ρ i) :
    compl σ = n = compl ρ.
  Proof.
    destruct (conv_cauchy σ n) as [m Hm]; destruct (conv_cauchy ρ n) as [k Hk].
    rewrite Hm, Hk; eauto using le_max_l, le_max_r.
  Qed.

  Lemma umet_complete_ext :
    (forall i, σ i == ρ i) -> compl σ == compl ρ.
  Proof.
    intros HEq; rewrite <- dist_refl; intros n; apply umet_complete_extn.
    intros i; revert n; rewrite dist_refl; apply HEq.
  Qed.

  Lemma umet_complete_const m : compl (fun _ => m) == m.
  Proof.
    symmetry; rewrite <- dist_refl; intros n.
    destruct (conv_cauchy (fun _ => m) n) as [k Hk]; rewrite Hk; eauto || reflexivity.
  Qed.

  (** Limits don't depend on prefixes of sequences. *)
  Lemma cut_complete_eq n :
    compl σ == compl (cutn σ n).
  Proof.
    rewrite <- dist_refl; intros m; destruct (conv_cauchy σ m) as [k Hk].
    destruct (conv_cauchy (cutn σ n) m) as [j Hj]; simpl in *.
    unfold cutn in *; rewrite Hj, Hk; [reflexivity | | apply le_max_l]; clear Hk Hj.
    apply _.
  Qed.

End ChainCompl.

(** Morphisms of metric spaces — non-expansive functions. *)
Record metric_morphism T U `{mT : metric T} `{mU : metric U} :=
  mkUMorph
    { met_morph :> T -=> U;
      met_morph_nonexp n : Proper (dist n ==> dist n) met_morph}.

Arguments mkUMorph [T U eqT mT eqT0 mU] _ _.
Arguments met_morph [T U] {eqT mT eqT0 mU} _.
Infix "-n>" := metric_morphism (at level 45, right associativity).

Global Instance metric_morphism_proper T U `{mT : metric T} `{mU : metric U} n (f: T -n> U):
  Proper (dist n ==> dist n) f.
Proof.
  now eapply met_morph_nonexp.
Qed.

Program Definition mkNMorph T U `{mT : metric T} `{mU : metric U} (f: T -> U)
        (NEXP : forall n, Proper (dist n ==> dist n) f) :=
  mkUMorph s[(f)] _.
Next Obligation.
  intros x y Heq.
  eapply dist_refl. intros n.
  eapply NEXP. rewrite Heq. reflexivity.
Qed.
Arguments mkNMorph [T U eqT mT eqT0 mU] _ _.
Notation "'n[(' f ')]'" := (mkNMorph f _).

Instance subrel_dist `{mT : metric T} n : subrelation equiv (dist n) | 5.
Proof.
  intros x y HEq; revert n; rewrite dist_refl; assumption.
Qed.

Section MMInst.
  Context `{mT : metric T} `{mU : metric U}.

  Global Program Instance nonexp_type : Setoid (T -n> U) | 5 :=
    mkType (fun f g => met_morph f == g).
  Next Obligation.
    split.
    + intros f x; reflexivity.
    + intros f g HS x; symmetry; apply HS.
    + intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.

  Global Program Instance nonexp_metric : metric (T -n> U) | 5 :=
    mkMetr (fun n f g => forall x, f x = n = g x).
  Next Obligation.
    intros f1 f2 EQf g1 g2 EQg; split; intros EQfg x; [symmetry in EQf, EQg |];
    rewrite (EQf x), (EQg x); apply EQfg.
  Qed.
  Next Obligation.
    fold equiv.
    split; [intros HEq t | intros HEq n].
    - rewrite <- dist_refl; intros n; apply HEq.
    - intros t; revert n; rewrite dist_refl; apply HEq.
  Qed.
  Next Obligation.
    intros f g HS x; symmetry; apply HS.
  Qed.
  Next Obligation.
    intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  Next Obligation.
    eauto using mono_dist.
  Qed.
  Next Obligation.
    apply dist_bound.
  Qed.

(*
  (** Note the set of morphisms, not the set of non-expansive maps. The distance is the supremum of pointwise distances. *)
  Global Program Instance fundistS : Dist (M -s> N) :=
    fun n f g => forall x, f x = n = g x.

  (** Note the set of non-expansive maps with the point-wise distance. *)
  Global Program Instance fundist : Dist (M -n> N) :=
    fun n f g => met_morph f = n = met_morph g.

  (** The hom-set (i.e. the set of non-expansive maps) is again a bisected ultrametic spaces. *)
  Global Instance MMmetric : metric (M -n> N) (D := fundist).
  Proof.
    split.
    + split; [intros HEq t | intros HEq n].
      * rewrite <- dist_refl; intros n; apply HEq.
      * intros t; revert n; rewrite dist_refl; apply HEq.
    + intros n f g HS x; symmetry; apply HS.
    +intros n f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
    + intros n f g HS x; simpl in *; eapply mono_dist; [| apply HS]; omega.
    + intros f g x; apply dist_bound.
    + intros n f1 f2 EQf g1 g2 EQg; split; intros EQfg x; [symmetry in EQf, EQg |];
      rewrite (EQf x), (EQg x); apply EQfg.
  Qed.
*)

End MMInst.

(** The next ones just seem to be "lemmas" stating that metric morphisms and morphisms preserve suitable equalities. *)
Instance mmorph_proper n `{mT : metric T} `{mU : metric U} :
  Proper (dist n ==> dist n ==> dist n) (met_morph (T := T) (U := U)).
Proof.
  intros f g HEq x y HEq'; etransitivity; [apply HEq | apply g, HEq'].
Qed.

Definition distS `{eqT : Setoid T} `{mU : metric U} n (f g : T -=> U) :=
  forall x, f x = n = g x.

Instance mmorph_properS n `{mT : metric T} `{mU : metric U} :
  Proper (distS n ==> equiv ==> dist n) (morph T U).
Proof.
  intros f g HEq x y HEq'; rewrite HEq'; apply HEq.
Qed.

Instance mmorph_inherit `{mT : metric T} `{mU : metric U} :
  Proper (equiv ==> equiv) (met_morph (T := T) (U := U)).
Proof. intros f g HEq; apply HEq. Qed.

Instance mmorph_extend `{mT : metric T} `{mU : metric U} n :
  Proper (dist n ==> distS n) (met_morph (T := T) (U := U)).
Proof. intros f g HEq x; rewrite (HEq x); reflexivity. Qed.

Instance morph_proper' n `{mT : metric T} `{mU : metric U} (f : T -n> U) :
  Proper (dist n ==> dist n) f := met_morph_nonexp _ _ _ _.

Ltac resp_dist := intros n; resp_set.

Section MCont.
  Context `{cT : cmetric T} `{cU : cmetric U} `{cV : cmetric V}.

  (** Definition of contractive functions. This works since the spaces are bisected. *)
  Class contractive (f : T -> U) := contr n : Proper (dist n ==> dist (S n)) f.

  Program Definition contractive_nonexp (f: T -> U) (fC: contractive f): T -n> U :=
    n[(f)].
  Next Obligation.
    intros t u EQ. eapply dist_mono, fC. assumption.
  Qed.
    

  (** Image of a Cauchy chain by a non-expansive function is another Cauchy sequence. *)
  Definition liftc (f : T -> U) (σ : chain T) : chain U := fun i => f (σ i).
  Arguments liftc f σ i / .
  Global Instance liftc_cauchy (f : T -n> U) (σ : chain T) {σc : cchain σ} :
    cchain (liftc f σ).
  Proof.
    intros n i j HLei HLej; simpl.
    rewrite (chain_cauchy σ); reflexivity || assumption.
  Qed.

  (** The same as before, only for two-argument functions. *)
  Definition binaryLimit (f : T -n> U -n> V) (σ : chain T) (ρ : chain U) : chain V :=
    fun i => f (σ i) (ρ i).
  Arguments binaryLimit f σ ρ i / .
  Global Instance binLim_cauchy (f : T -n> U -n> V) (σ : chain T) (ρ : chain U) {σc : cchain σ} {ρc : cchain ρ} : cchain (binaryLimit f σ ρ).
  Proof.
    intros n i j HLei HLej; simpl.
    rewrite (chain_cauchy σ), (chain_cauchy ρ); reflexivity || assumption.
  Qed.

  (** Non-expansive functions preserve limits, i.e. are continuous. *)
  Lemma nonexp_continuous (f : T -n> U) (σ : chain T) (σc : cchain σ) :
    f (compl σ) == compl (liftc f σ).
  Proof.
    rewrite <- dist_refl; intros n; destruct (conv_cauchy σ n) as [k B].
    destruct (conv_cauchy (liftc f σ) n) as [m A]; simpl in *.
    specialize (B (max m k) _); specialize (A (max m k) _).
    rewrite B, A; reflexivity.
  Qed.

  Local Obligation Tactic := intros; resp_set || program_simpl.

  (** Composition of non-expansive maps is non-expansive. *)
  Program Definition umcomp (f : U -n> V) (g : T -n> U) : T -n> V :=
    n[(f << g)].

  Program Definition lift2m (f : T -=> U -=> V) p q : (T -n> U -n> V) :=
    mkUMorph s[(fun x => mkUMorph (f x) (p x))] q.

End MCont.

Infix "<M<" := umcomp (at level 35).

Section MCompP.
  Context `{cT : cmetric T} `{cU : cmetric U} `{cV : cmetric V} `{cW : cmetric W}.
  
  (** Composition preserves distances. *)
  Global Instance ndist_umcomp n :
    Proper (dist n (T := U -n> V) ==> dist n ==> dist n) umcomp.
  Proof. intros f f' HEq g g' HEq' x; simpl; rewrite HEq, HEq'; reflexivity. Qed.

  Lemma lift_comp (f : U -n> V) (g : T -n> U) (σ : chain T) {σc : cchain σ} :
    compl (liftc f (liftc g σ)) == compl (liftc (f <M< g) σ).
  Proof.
    apply umet_complete_ext; try apply _; intros i; reflexivity.
  Qed.

  Lemma mcomp_assoc (f : V -n> W) (g : U -n> V) (h : T -n> U) :
    f <M< (g <M< h) == (f <M< g) <M< h.
  Proof. intros x; reflexivity. Qed.

  Local Obligation Tactic := intros; resp_set || program_simpl.

  (** Composition as a _non-expansive_ morphism itself. This then shows that the
  category of bisected spaces is enriched in itself. *)
  Program Definition comp : (U -n> V) -n> (T -n> U) -n> T -n> V :=
    lift2m (lift2s (fun f g => f <M< g) _ _) _ _.

  Program Definition umid : T -n> T := n[(mid _)].

  Program Definition umconst x : T -n> U := n[(mconst x)].

  Global Program Instance umconst_contractive m : contractive (umconst m).

  Program Definition precomp_ne (f : T -n> U) : (U -n> V) -n> (T -n> V) :=
    n[(fun g => g <M< f)].

  Program Definition postcomp_ne (f : T -n> U) : (V -n> T) -n> (V -n> U) :=
    n[(fun g => f <M< g)].

End MCompP.

Arguments umid T {eqT mT}.

(** Single element space and the distance on it. *)
Program Instance unit_metric : metric unit :=
  mkMetr (fun _ _ _ => True).
Next Obligation. tauto. Qed.

(** The unit space is complete. *)
Program Instance unit_cmetric : cmetric unit :=
  mkCMetr (fun _ _ => tt).
Next Obligation.
  intros n; exists 0; intros k HLe; destruct (σ k); reflexivity.
Qed.

Section Iteration.
  Context `{mT : metric T}.

  Fixpoint iter n (f : T -> T) :=
    match n with
      | O => id
      | S n => fun x => f (iter n f x)
    end.

  (** Iteration of a non-expansive function again gives a non-expansive function. *)

  Program Definition itern n (f : T -n> T) : T -n> T :=
    n[(iter n f)].
  Next Obligation.
    induction n; simpl; [apply _ | resp_set].
  Qed.

  Lemma iter_plus f m n x : iter m f (iter n f x) = iter (m + n) f x.
  Proof. induction m; simpl; [reflexivity | f_equal; assumption]. Qed.

  (** If a function is contractive then after sufficiently many iterations it
  maps all elements closer than 2⁻ⁿ. *)
  Lemma bounded_contractive_n f {HC : contractive f} n m x y (HLe : n <= m) :
    iter m f x = n = iter m f y.
  Proof.
    revert m x y HLe; induction n; intros; [apply dist_bound |].
    destruct m; [inversion HLe |]; simpl; apply HC, IHn; omega.
  Qed.

  Global Instance cfix f {HC : contractive f} x : cchain (fun n => iter n f x).
  Proof.
    unfold cchain; intros.
    cutrewrite (i = n + (i - n)); [rewrite <- iter_plus | omega].
    cutrewrite (j = n + (j - n)); [rewrite <- iter_plus | omega].
    apply bounded_contractive_n; [assumption | auto].
  Qed.

End Iteration.

Section Fixpoints.
  Context `{cT : cmetric T}.

  (** A fixed point of a contractive f is the limit of the iterations of the
  function. This seemingly depends on the starting point x. *)
  Definition fixp f {HC : contractive f} x := compl (fun n => iter n f x).

  (** Stating that the proposed fixed point is in fact a fixed point. *)
  Lemma fixp_eq f x {HC : contractive f} : fixp f x == f (fixp f x).
  Proof.
    pose (f' := contractive_nonexp _ HC).
    change (fixp f' x == f' (fixp f' x)).
    rewrite <- dist_refl; intros n; unfold fixp.
    destruct (conv_cauchy (fun n => iter n f' x) n) as [m Hm].
    rewrite (Hm (S (max n m))), (Hm (max n m)) at 1; simpl; reflexivity || apply _.
  Qed.

  Lemma fixp_iter f x i {HC : contractive f} : fixp f x == iter i f (fixp f x).
  Proof.
    pose (f' := contractive_nonexp _ HC).
    change (fixp f' x == iter i f' (fixp f' x)).
    induction i; [reflexivity |].
    etransitivity; [eapply fixp_eq|].
    rewrite IHi at 1. reflexivity.
  Qed.

  (** Fixed points are unique, i.e. the fixp does not depend on the starting point of the iteration. *)
  Lemma fixp_unique f x y {HC : contractive f} : fixp f x == fixp f y.
  Proof.
    rewrite <- dist_refl; intros n; unfold fixp.
    destruct (conv_cauchy (fun n => iter n f x) n) as [mx Hmx].
    destruct (conv_cauchy (fun n => iter n f y) n) as [my Hmy].
    rewrite (Hmx (max n (max mx my))), Hmy;
      [ rewrite bounded_contractive_n | ..]; reflexivity || apply _.
  Qed.

  (** This lemma states that fixp is non-expansive in f. *)
  Lemma fixp_ne (f f' : T -n> T) {HC : contractive f} (HC' : contractive f') x x' n  (HEq : f = n = f') :
    fixp f x = n = fixp f' x'.
  Proof.
    rewrite fixp_unique with (x := x') (y := x).
    clear x'; unfold fixp; destruct (conv_cauchy (fun n => iter n f x) n) as [m Hm].
    destruct (conv_cauchy (fun n => iter n f' x) n) as [k Hk].
    rewrite (Hm (max m k)), (Hk (max m k)); try apply _; [].
    clear Hm Hk; induction (max m k); simpl; [reflexivity |].
    rewrite IHn0; apply HEq.
  Qed.

  (** From the non-expansiveness it also follows that fixp preserves equality of f. *)
  Lemma fixp_equiv (f f' : T -n> T) {HC : contractive f} (HC' : contractive f') x x' (HEq : f == f') :
    fixp f x == fixp f' x'.
  Proof.
    rewrite <- dist_refl; intros n; apply fixp_ne.
    rewrite HEq; reflexivity.
  Qed.

  (** The above properties should be enough to reason about fixpoints, so we make the definition opaque *)
  Global Opaque fixp.

End Fixpoints.

Section ChainApps.
  Context `{cT : cmetric T} `{cU : cmetric U} (σ : chain (T -n> U)) {σc : cchain σ}.

  (** A cauchy chain applied to an element gives another Cauchy chain. *)
  Global Instance chain_app x : cchain (fun i => σ i x).
  Proof. unfold cchain; intros; rewrite (chain_cauchy σ); reflexivity || assumption. Qed.

  Instance nonexp_lub n : Proper (dist n ==> dist n) (fun x => compl (fun i => σ i x)).
  Proof.
    intros x y HEq; destruct (conv_cauchy (fun i => σ i x) n) as [mx Hmx].
    destruct (conv_cauchy (fun i => σ i y) n) as [my Hmy].
    rewrite Hmx, Hmy; simpl; [rewrite HEq; reflexivity | ..]; auto using le_max_r, le_max_l.
  Qed.

  (** Given a Cauchy chain of functions we get a non-expansive function by
  taking limits starting at different points. Used to show that the hom-set is a
  complete metric space. *)
  Program Definition fun_lub : T -n> U :=
    n[(fun x => compl (fun i => σ i x))].

End ChainApps.

Section NonexpCMetric.
  Context `{cT : cmetric T} `{cU : cmetric U}.

  (** THe set of non-expansive morphisms between two complete metric spaces is again a complete metric space. *)
  Global Program Instance nonexp_cmetric : cmetric (T -n> U) | 5 :=
    mkCMetr fun_lub.
  Next Obligation.
    intros n; exists n; intros m HLe x.
    destruct (conv_cauchy (fun i => σ i x) n) as [k Hk].
    rewrite (Hk (max m k)), (chain_cauchy σ); [reflexivity |..]; apply _.
  Qed.

End NonexpCMetric.

(** Product of two complete metric spaces. *)
Section MetricProducts.
  Context `{cT : cmetric T} `{cU : cmetric U} `{cV : cmetric V}.

  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Definition prod_dist n (p1 p2 : U * V) :=
    fst p1 = n = fst p2 /\ snd p1 = n = snd p2.
  Global Arguments prod_dist n p1 p2 /.

  Global Program Instance prod_metric : metric (U * V) := mkMetr prod_dist.
  Next Obligation.
    intros [a1 b1] [a2 b2] [Ha Hb] [a3 b3] [a4 b4] [Ha' Hb']; simpl in *.
    rewrite Ha, Hb, Ha', Hb'; reflexivity.
  Qed.
  Next Obligation.
    split; intros HEq.
    + split; rewrite <- dist_refl; intros n; destruct (HEq n); assumption.
    + intros n; split; revert n; rewrite dist_refl; destruct HEq; assumption.
  Qed.
  Next Obligation.
    intros [a1 b1] [a2 b2] [Ha Hb]; split; symmetry; assumption.
  Qed.
  Next Obligation.
    intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha23 Hb23]; split; etransitivity; eassumption.
  Qed.
  Next Obligation.
    destruct H; split; eapply mono_dist; try eassumption; auto.
  Qed.
  Next Obligation.
    split; apply dist_bound.
  Qed.

  Global Instance prod_proper_n n : Proper (dist n ==> dist n ==> dist n) (@pair U V).
  Proof. intros a a' Ha b b' Hb; split; assumption. Qed.

  Global Instance mfst_proper_n n : Proper (dist n ==> dist n) (@fst U V).
  Proof. intros [a1 b1] [a2 b2] [Ha Hb]; assumption. Qed.

  Global Instance msnd_proper_n n : Proper (dist n ==> dist n) (@snd U V).
  Proof. intros [a1 b1] [a2 b2] [Ha Hb]; assumption. Qed.

  Definition Mfst : U * V -n> U := n[(mfst)].
  Definition Msnd : U * V -n> V := n[(msnd)].

  Program Definition Mprod (f : T -n> U) (g : T -n> V) : T -n> U * V :=
    n[(mprod f g)].
  Next Obligation.
    intros x y HEq; simpl; rewrite HEq; split; reflexivity.
  Qed.

  Lemma Mprod_fst f g : Mfst <M< Mprod f g == f.
  Proof. intros x; reflexivity. Qed.

  Lemma Mprod_snd f g : Msnd <M< Mprod f g == g.
  Proof. intros x; reflexivity. Qed.

  Lemma Mprod_unique (f : T -n> U) (g : T -n> V) (h : T -n> U * V) :
    Mfst <M< h == f -> Msnd <M< h == g -> h == Mprod f g.
  Proof. intros HL HR; apply (mprod_unique HL HR). Qed.

  (** Product of complete spaces is again a complete space. *)
  Definition prod_compl (σ : chain (U * V)) (σc : cchain σ) :=
    (compl (liftc Mfst σ), compl (liftc Msnd σ)).
  Arguments prod_compl σ σc /.

  Global Program Instance prod_cmetric : cmetric (U * V) :=
    mkCMetr prod_compl.
  Next Obligation.
    intros n; destruct (conv_cauchy (liftc Mfst σ) n) as [mfst Hfst].
    destruct (conv_cauchy (liftc Msnd σ) n) as [msnd Hsnd].
    exists (max mfst msnd); intros k HLe; split; simpl in *;
      [apply Hfst | apply Hsnd]; eauto using le_max_l, le_max_r, le_trans.
  Qed.

End MetricProducts.

(** Indexed product, very similar to binary product. The metric is pointwise, the supremum. *)
Section MetricIndexed.
  Context {I : Type} {P : I -> Mtyp}.

  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Definition distI n (a b : forall i, P i) := forall i, mprojI i a = n = mprojI i b.
  Global Arguments distI n a b /.

  Global Program Instance prodI_metr : metric (forall i, P i) :=
    mkMetr distI.
  Next Obligation.
    intros x y EQxy u v EQuv; split; intros EQ i; [symmetry in EQxy, EQuv |]; rewrite (EQxy i), (EQuv i); apply EQ.
  Qed.
  Next Obligation.
    split; intros HEq n.
    + rewrite <- dist_refl; intros m; apply (HEq m).
    + intros i; revert n; rewrite dist_refl; apply HEq.
  Qed.
  (*Next Obligation.
    intros x y HS i; symmetry; apply HS.
  Qed.*)
  Next Obligation.
    intros x y z Hxy Hyz i; etransitivity; [apply Hxy | apply Hyz].
  Qed.
  Next Obligation.
    eapply mono_dist, H; auto.
  Qed.
  Next Obligation.
    apply dist_bound.
  Qed.

  Program Definition MprojI (i : I) : (forall i, P i) -n> P i :=
    n[(mprojI i)].

  Context `{mT : metric T}.
  Program Definition MprodI (f : forall i, T -n> P i) : T -n> forall i, P i :=
    n[(mprodI f)].

  Lemma MprodI_proj f i : MprojI i <M< MprodI f == f i.
  Proof. intros x; reflexivity. Qed.

  Lemma MprodI_unique f g (HEq : forall i, MprojI i <M< g == f i) : g == MprodI f.
  Proof. apply (mprodI_unique f g HEq). Qed.

End MetricIndexed.

(** Indexed product of complete spaces is again a complete space. *)
Section CompleteIndexed.
  Context {I : Type} {P : I -> cmtyp}.

  Definition prodI_compl (σ : chain (forall i, P i)) (σc : cchain σ) (i : I) :=
    compl (liftc (MprojI i) σ).
  Arguments prodI_compl σ σc i /.
  Global Program Instance prodI_cmetric : cmetric (forall i, P i) :=
    mkCMetr prodI_compl.
  Next Obligation.
    intros n; exists n; intros m HLe i.
    destruct (conv_cauchy (liftc (MprojI i) σ) n) as [k Hk]; simpl in *.
    rewrite  Hk; [| apply le_max_r]; clear Hk.
    unfold liftc; apply σc; eauto using le_trans, le_max_l.
  Qed.

End CompleteIndexed.

Section Chains_of_IProds.
  Context {I : Type} {P : I -> cmtyp} (σ : chain (forall i, P i)) {σc : cchain σ}.

  Global Instance dep_chain_app (x : I) : cchain (fun n => σ n x).
  Proof.
    unfold cchain; intros; apply σc; assumption.
  Qed.

  Lemma dep_chain_compl (x : I) :
    compl σ x == compl (fun n => σ n x).
  Proof.
    apply umet_complete_ext; intros n; reflexivity.
  Qed.

End Chains_of_IProds.

Section ComplSetup.
  Context `{cT : cmetric T} `{cU : cmetric U} (σ : chain T) (ρ : chain U) {σc : cchain σ} {ρc : cchain ρ}.

  Definition chain_pair n := (σ n, ρ n).
  Global Instance cchain_pair : cchain chain_pair.
  Proof. split; simpl; eapply chain_cauchy; assumption. Qed.

  (** The limit in the product is computed pointwise, i.e. the limit is the pair
  of limits computed in original spaces. *)
  Lemma pair_limit : compl (chain_pair) == (compl σ, compl ρ).
  Proof. split; simpl; apply umet_complete_ext; intros i; reflexivity. Qed.

End ComplSetup.

(** The subspace defined by P is chain complete. *)
Class LimitPreserving `{cT : cmetric T} (P : T -> Prop) :=
  lim_pres : forall (σ : chain T) (σc : cchain σ), (forall i, P (σ i)) -> P (compl σ).

(** The set of contractive functions is complete in the set of non-expansive ones. *)
Instance contractive_complete `{cT : cmetric T} `{cU : cmetric U} :
  LimitPreserving (fun f : T -n> U => contractive f).
Proof.
  intros σ σc HC n x y HEq; destruct (conv_cauchy σ (S n)) as [m Hm].
  rewrite (Hm m); [apply HC |]; trivial.
Qed.

Section OptM.
  Context `{mT : metric T}.

  Definition option_dist n (x y : option T) :=
    match n with
      | O => True
      | S _ => match x, y with
                 | Some x, Some y => x = n = y
                 | None, None => True
                 | Some _, None => False
                 | None, Some _ => False
               end
      end.

  Global Program Instance option_metric : metric (option T) :=
    mkMetr option_dist.
  Next Obligation.
    destruct n as [| n]; intros [x |] [y |] EQxy [u |] [v |] EQuv; simpl in *; try (contradiction || reflexivity); [].
    unfold equiv in EQxy, EQuv; simpl in *; rewrite EQxy, EQuv; reflexivity.
  Qed.
  Next Obligation.
    split; intros HEq.
    - destruct x; destruct y; try (contradiction (HEq 1) || reflexivity); [].
      unfold equiv; simpl; rewrite <- dist_refl; intros n.
      specialize (HEq (S n)); eapply mono_dist, HEq; auto.
    - intros [| n]; [reflexivity |].
      destruct x; destruct y; try (contradiction HEq || reflexivity); simpl in *.
      generalize (S n); rewrite dist_refl; assumption.
  Qed.
  Next Obligation.
    destruct n as [| n]; intros [x |] [y |] HS; try (contradiction HS || reflexivity);
    simpl; symmetry; assumption.
  Qed.
  Next Obligation.
    revert n; intros [| n] [x |] [y |] [z |] Hxy Hyz; try (contradiction || reflexivity);
    simpl; etransitivity; [apply Hxy | apply Hyz].
  Qed.
  Next Obligation.
    destruct n as [n |]; destruct x as [x |]; destruct y as [y |]; try (contradiction H || reflexivity);
    simpl; eapply mono_dist, H; auto.
  Qed.

End OptM.

(** Subspaces. *)
Section Submetric.
  Context `{mT : metric T} {P : T -> Prop}.
  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Definition subset_Dist n (x y : {e : T | P e}) := proj1_sig x = n = proj1_sig y.
  Global Arguments subset_Dist n x y /.

  Global Program Instance sub_metric : metric {e : T | P e} :=
    mkMetr subset_Dist.
  Next Obligation.
    intros [x Hx] [y Hy] EQxy [u Hu] [v Hv] EQuv; unfold equiv in EQxy, EQuv; simpl in *.
    rewrite EQxy, EQuv; reflexivity.
  Qed.
  Next Obligation.
    apply dist_refl.
  Qed.
  Next Obligation.
    intros [x Hx] [y Hy] [z Hz] Hxy Hyz; simpl in *; etransitivity; eassumption.
  Qed.
  Next Obligation.
    eapply mono_dist, H; auto.
  Qed.
  Next Obligation.
    apply dist_bound.
  Qed.

  Program Definition inclM : {e : T | P e} -n> T :=
    n[(mincl)].

  Context {U} `{mU : metric U}.

  Program Definition inheritM (f : U -n> T) (HAll : forall n, P (f n)) :=
    n[(minherit f HAll)].

  Lemma forgetM_mono f g (HF : inclM <M< f == inclM <M< g) : f == g.
  Proof. apply mforget_mono, HF. Qed.

End Submetric.

Section SubCMetric.
  Context `{cT : cmetric T} {P : T -> Prop} {C : LimitPreserving P}.

  (** If a space defined by P is complete (assumption [ccomplete P]) then it
  already contains the limits of its Cauchy chains. *)
  Lemma subchainlubP (σ : chain {x : T | P x}) {σc : cchain σ} :
    P (compl (liftc inclM σ)).
  Proof. apply C; intros i; unfold liftc; destruct (σ i); simpl; assumption. Qed.

  Definition sub_compl (σ : chain {x : T | P x}) {σc : cchain σ} :=
    exist P (compl (liftc inclM σ)) (subchainlubP σ).
  Global Program Instance sub_cmetric : cmetric {x : T | P x} :=
    mkCMetr sub_compl.
  Next Obligation.
    intros n; simpl; destruct (conv_cauchy (liftc inclM σ) n) as [m Hm].
    exists m; intros k HLe; apply (Hm _ HLe).
  Qed.

End SubCMetric.

Section Exponentials.
  Context `{mT : metric T} `{mU : metric U} `{mV : metric V}.
  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Program Definition uncurry (f : T -n> U -n> V) : (T * U -n> V) :=
    n[(fun p => f (fst p) (snd p))].
  Next Obligation.
    intros [a1 b1] [a2 b2] [Ha Hb]; simpl in *.
    rewrite Ha, Hb; reflexivity.
  Qed.

  Program Definition curryM (f : T * U -n> V) : T -n> U -n> V := lift2m (mcurry f) _ _.

  Context `{mW : metric W}.

  Definition prodM_map (f : T -n> U) (g : V -n> W) := Mprod (f <M< Mfst) (g <M< Msnd).

  Program Definition evalM : (T -n> U) * T -n> U :=
    n[(meval << mprod_map s[(met_morph (U := U))] (mid _))].
  Next Obligation.
    intros f g HEq; simpl; rewrite !HEq at 1; reflexivity.
  Qed.

End Exponentials.

Section ExponentialProps.
  Context `{mT : metric T} `{mU : metric U} `{mV : metric V}.

  Lemma curryMCom (f : T * U -n> V) : f == evalM <M< prodM_map (curryM f) (umid _).
  Proof. intros [a b]; reflexivity. Qed.

  Lemma curryM_unique (f : T * U -n> V) g (HEq : f == evalM <M< prodM_map g (umid _)) :
    g == curryM f.
  Proof. intros a b; simpl; rewrite HEq; reflexivity. Qed.

End ExponentialProps.

Lemma nonexp_cont2 `{cT : cmetric T} `{cU : cmetric U} `{cV : cmetric V} (f : T -n> U -n> V) (σ : chain T) (ρ : chain U) {σc : cchain σ} {ρc : cchain ρ} :
  f (compl σ) (compl ρ) == compl (binaryLimit f σ ρ).
Proof.
  assert (HT := nonexp_continuous (uncurry f) (chain_pair σ ρ) _).
  rewrite pair_limit in HT at 1; simpl in HT; rewrite HT; apply umet_complete_ext; intros i; clear HT.
  reflexivity.
Qed.

(** Discrete spaces are proper metric spaces (discrete meaning that the distance
    is 1 if elements are diffent and 0 for equal elements. Equality here is
    propositional Coq equality. *)
Section DiscreteMetric.
  Context {T : Type} {T_type : Setoid T}.

  Definition discreteDist n (x y : T) :=
    match n with
        O => True
      | _ => x == y
    end.
  Global Arguments discreteDist n x y / .
  
  Program Instance discreteMetric : metric T := mkMetr discreteDist.
  Next Obligation.
    intros x y Heq x' y' Heq'. split; (destruct n as [|n]; [reflexivity|simpl]).
    - intros Heqx. rewrite <-Heq, <-Heq'. assumption.
    - intros Heqy. rewrite Heq, Heq'. assumption.
  Qed.
  Next Obligation.
    split; intros Heq.
    - now apply (Heq 1).
    - intros [|n]; tauto.
  Qed.
  Next Obligation.
    destruct n as [| n]; intros x y HS; simpl in *; [| symmetry]; tauto.
  Qed.
  Next Obligation.
    destruct n as [| n]; intros x y z Hxy Hyz; simpl in *; [| etransitivity]; eauto.
  Qed.
  Next Obligation.
    destruct n; tauto.
  Qed.

  Definition discreteCompl (σ : chain T) {σc : cchain σ} := σ 1.

  Program Instance discreteCMetric : cmetric T := mkCMetr discreteCompl.
  Next Obligation.
    intros n; exists 1; simpl; intros [| i] HLe; [inversion HLe |].
    destruct n as [| n]; [exact I |].
    assert (HT := chain_cauchy σ _ 1 (S i) 1). rewrite HT.
    reflexivity.
  Qed.

End DiscreteMetric.

Section Option.
  Context `{cT : cmetric T}.

  Program Definition unSome (σ : chain (option T)) {σc : cchain σ} (HNE : σ 1 <> None) : chain T :=
    fun i => match σ (S i) with
               | None => False_rect _ _
               | Some v => v
             end.
  Next Obligation.
    specialize (σc 1 1 (S i)); rewrite <- Heq_anonymous in σc.
    destruct (σ 1) as [v |]; [contradiction σc; auto with arith | contradiction HNE; reflexivity].
  Qed.

  Instance unSome_c (σ : chain (option T)) {σc : cchain σ} HNE : cchain (unSome σ HNE).
  Proof.
    intros [| k] n m HLE1 HLE2; [apply dist_bound |]; unfold unSome.
    generalize (@eq_refl _ (σ (S n))); pattern (σ (S n)) at 1 3.
    destruct (σ (S n)) as [v |]; simpl; intros EQn.
    - generalize (@eq_refl _ (σ (S m))); pattern (σ (S m)) at 1 3.
      destruct (σ (S m)) as [v' |]; simpl; intros EQm.
      + specialize (σc (S k) (S n) (S m)); rewrite <- EQm, <- EQn in σc.
        apply σc; auto with arith.
      + exfalso; specialize (σc 1 1 (S m)); rewrite <- EQm in σc.
        destruct (σ 1) as [v' |]; [contradiction σc; auto with arith | contradiction HNE; reflexivity].
    - exfalso; specialize (σc 1 1 (S n)); rewrite <- EQn in σc.
      destruct (σ 1) as [v |]; [contradiction σc; auto with arith | contradiction HNE; reflexivity].
  Qed.

  Program Definition option_compl (σ : chain (option T)) {σc : cchain σ} :=
    match σ 1 with
      | None => None
      | Some v => Some (compl (unSome σ _))
    end.

  Global Program Instance option_cmt : cmetric (option T) := mkCMetr option_compl.
  Next Obligation.
    intros [| n]; [exists 0; intros; apply dist_bound | unfold option_compl].
    generalize (@eq_refl _ (σ 1)) as EQ1; pattern (σ 1) at 1 3; destruct (σ 1) as [v |]; intros.
    - assert (HT := conv_cauchy (unSome σ (option_compl_obligation_1 _ _ _ EQ1)) (S n)).
      destruct HT as [k HT]; exists (max k (S n)); intros.
      destruct (σ i) as [vi |] eqn: EQi; [unfold dist; simpl; rewrite (HT i) by eauto with arith | exfalso].
      + unfold unSome; generalize (@eq_refl _ (σ (S i))); pattern (σ (S i)) at 1 3.
        destruct (σ (S i)) as [vsi |]; intros EQsi; clear HT; [| exfalso].
        * assert (HT : S n <= i) by eauto with arith.
          specialize (σc (S n) (S i) i); rewrite EQi, <- EQsi in σc.
          apply σc; auto with arith.
        * specialize (σc 1 1 (S i)); rewrite <- EQ1, <- EQsi in σc.
          apply σc; auto with arith.
      + clear HT; specialize (σc 1 1 i); rewrite <- EQ1, EQi in σc.
        apply σc; auto with arith.
        rewrite <- HLe, <- Max.le_max_r; auto with arith.
    - exists 1; intros.
      destruct (σ i) as [vi |] eqn: EQi; [| reflexivity].
      specialize (σc 1 1 i); rewrite <- EQ1, EQi in σc.
      apply σc; auto with arith.
  Qed.

End Option.

Arguments dist {_ _ _} _ _ _ /.

(* We have several users of this, so deifne it centrally *)
Module NatDec.
  Definition U := nat.
  Definition eq_dec := eq_nat_dec.
End NatDec.

Module D := Coq.Logic.Eqdep_dec.DecidableEqDep(NatDec).
