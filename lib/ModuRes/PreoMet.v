Require Import ssreflect.
Require Export Predom MetricCore.

Generalizable Variables T U V W X Y.

Section PreCBUmet.
  Context (T : Type) `{cmT : cmetric T}.

  Definition respect_chain (le : relation T) :=
    forall (σ ρ : chain T) (σc : cchain σ) (ρc : cchain ρ),
      (forall i, le (σ i) (ρ i)) -> le (compl σ) (compl ρ).

  Class pcmType {pTA : preoType T} :=
    { pcm_respC :  respect_chain pord }.

End PreCBUmet.


Record monoMet_morphism T U `{pcmT : pcmType T} `{pcmU : pcmType U} := mkMUMorph
  { mu_morph :> T -n> U;
    mu_mono  :  Proper (pord ==> pord) mu_morph}.

Arguments mkMUMorph [T U] {_ _ _ _ _ _ _ _ _ _} _ _.
Arguments mu_morph  [T U] {_ _ _ _ _ _ _ _ _ _} _.
Arguments mu_mono  {_ _} {_ _ _ _ _ _ _ _ _ _} _ {_ _} _.

Infix "-m>" := monoMet_morphism (at level 45, right associativity) : pumet_scope.
Notation "'m[(' f ')]'" := (mkMUMorph n[(f)] _).
Delimit Scope pumet_scope with pm.
Open Scope pumet_scope.

Section Morph_Props.
  Context `{pcmT : pcmType T} `{pcmU : pcmType U} `{pcmV : pcmType V}.
  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Program Definition pcomp (f : U -m> V) (g : T -m> U) :=
    m[(f <M< g)].
  Next Obligation.
    intros x y HSub; apply mu_mono; now apply mu_mono.
  Qed.

  Program Definition pid := m[(umid _)].

End Morph_Props.

Notation "f ∘ g" := (pcomp f g) (at level 40, left associativity) : pumet_scope.
Arguments pid V {_ _ _ _ _}.

Section PUMMorphProps1.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.
  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Definition PMEquiv (x y : T -m> U) := mu_morph x == mu_morph y.

  Global Instance PMEquivE: Equivalence PMEquiv.
  Proof.
    split.
    - intros f x; simpl; reflexivity.
    - intros f g Hfg x; simpl; symmetry; apply Hfg.
    - intros f g h Hfg Hgh x; simpl; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  
  Global Program Instance PMtypeM : Setoid (T -m> U) | 5 := mkType PMEquiv.

  Definition PMDist n (f g : T -m> U) := (mu_morph f) = n = (mu_morph g).

  Global Program Instance PMMetric : metric (T -m> U) | 5 := mkMetr PMDist.
  Next Obligation.
    intros f g EQfg h i EQhi; split; intros EQ x; [symmetry in EQfg, EQhi |]; rewrite -> (EQfg x), (EQhi x); apply EQ.
  Qed.
  Next Obligation.
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
    intros t; simpl in *; eapply mono_dist; [| apply H]; omega.
  Qed.
  Next Obligation.
    intros t; apply dist_bound.
  Qed.

  Global Instance ccm (σ : chain (T -m> U)) {σc : cchain σ} : cchain (fun i => mu_morph (σ i)).
  Proof.
    unfold cchain; intros; apply σc; assumption.
  Qed.

  Global Program Instance PMpreoT : preoType (T -m> U) | 5 :=
    mkPOType (fun f g => forall x, (f x ⊑ g x)%pd) _.
  Next Obligation.
    split.
    - intros x; simpl; reflexivity.
    - intros f g h Hfg Hgh; simpl; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  Next Obligation.
    move=> f1 f2 Rf g1 g2 Rg H t.
    rewrite -(Rf t) -(Rg t).
    exact: H.
  Qed.

  Global Instance PM_proper (f : T -m> U) : Proper (pord ==> pord) f.
  Proof. apply mu_mono. Qed.

  Definition PMasMono (f : T -m> U) : (T -m> U)%pd :=
    mkMMorph (mu_morph f) _.

  Program Definition mu_morph_ne : (T -m> U) -n> (T -n> U) :=
    n[(mu_morph (U := U))].
  Next Obligation.
    intros x y HEq t; apply HEq.
  Qed.

  Program Definition PMCompl (σ : chain (T -m> U)) (σc : cchain σ) : T -m> U :=
    mkMUMorph (compl (liftc mu_morph_ne σ)) _.
  Next Obligation.
    intros x y HSub; simpl.
    eapply pcm_respC; [assumption |]; intros; simpl.
    rewrite -> HSub; reflexivity.
  Qed.

  Global Program Instance PMcmetric : cmetric (T -m> U) | 5 :=
    mkCMetr PMCompl.
  Next Obligation.
    apply (conv_cauchy (liftc mu_morph_ne σ)).
  Qed.

  Arguments PMEquiv _ _ /.

  Global Instance mon_morph_preoT : pcmType (T -m> U) | 5.
  Proof.
    clear; split.
    intros f g fc gc Hc x; simpl; eapply pcm_respC; try eassumption.
    intros n; apply Hc.
  Qed.

  Global Instance pord_pmu :
    Proper (pord ==> pord ==> pord) (mu_morph (T := T) (U := U)).
  Proof.
    intros f g HSub x y HSub'; etransitivity; [apply HSub | apply g, HSub'].
  Qed.

  Definition ordS (f g : T -=> U) := forall x, (f x ⊑ g x)%pd.
  Definition ordN (f g : T -n> U) := forall x, (f x ⊑ g x)%pd.
  Global Instance pord_extend_morph :
    Proper (ordN ==> ordS) (met_morph (T := T) (U := U)).
  Proof.
    intros f g HS; apply HS.
  Qed.

  Global Instance pord_extend_met :
    Proper (pord (T := T -m> U) ==> ordN) (mu_morph (U := U)).
  Proof.
    intros f g HS; apply HS.
  Qed.

  Global Instance pord_morph :
    Proper (ordS ==> equiv ==> pord) (morph T U).
  Proof.
    intros f g HS x y HS'; etransitivity; [apply HS |].
    eapply preoC; try assumption; [reflexivity | apply g; rewrite <- HS' |]; reflexivity.
  Qed.
    
  Global Instance pcm_equiv_inherit :
    Proper (equiv (A := T -m> U) ==> equiv (A := T -n> U)) (mu_morph (U := U)).
  Proof. intros f g HEq; apply HEq. Qed.

  Global Instance pcm_dist_inherit n :
    Proper (dist n (T := T -m> U) ==> dist n (T := T -n> U)) (mu_morph (U := U)).
  Proof. intros f g HEq; apply HEq. Qed.


End PUMMorphProps1.

Notation "x ⊑ y" := (pord x y) (at level 70, no associativity) : pumet_scope.

Section CompProps.
  Context T U V `{pcmT : pcmType T} `{pcmU : pcmType U} `{pcmV : pcmType V}.

(*
  Global Instance pord_equiv : Proper (equiv ==> equiv ==> iff) pord.
  Proof.
    intros a1 a2 EQa b1 b2 EQb; split; intros Sub; [symmetry in EQa, EQb |]; rewrite -> EQa, EQb; assumption.
  Qed.
*)

  Global Instance pcomp_inherit :
    Proper (equiv (A := T -m> U) ==> equiv ==> equiv) pcomp.
  Proof.
    intros f f' Eqf g g' Eqg x; simpl; rewrite -> Eqf, Eqg; reflexivity.
  Qed.

  Global Instance pcomp_inherit_dist n :
    Proper (dist (T := T -m> U) n ==> dist n ==> dist n) pcomp.
  Proof.
    intros f f' Eqf g g' Eqg x; simpl; rewrite -> Eqf, Eqg; reflexivity.
  Qed.

  Context W `{pcmW : pcmType W}.

  Lemma pcomp_assoc (f : V -m> W) (g : U -m> V) (h : T -m> U) :
    f ∘ (g ∘ h) == (f ∘ g) ∘ h.
  Proof. intros x; reflexivity. Qed.

  Lemma pcomp_pid_right (f : T -m> U) :
    f ∘ (pid _) == f.
  Proof. intros x; reflexivity. Qed.

  Lemma pcomp_pid_left (f : T -m> U) :
    (pid _) ∘ f == f.
  Proof. intros x; reflexivity. Qed.

  Local Obligation Tactic := intros; resp_set || resp_dist || mono_resp || eauto.

  Program Definition precomp_mne (f : T -m> U) : (U -m> V) -m> (T -m> V) :=
    m[(fun g => g ∘ f)].

  Program Definition postcomp_mne (f : T -m> U) : (V -m> T) -m> (V -m> U) :=
    m[(fun g => f ∘ g)].

End CompProps.

Arguments precomp_mne  {T U V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} f.
Arguments postcomp_mne {T U V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} f.
Notation "f ▹" := (precomp_mne f) (at level 30) : pumet_scope.
Notation "◃ f" := (postcomp_mne f) (at level 30) : pumet_scope.

Section MMorphProps2.
  Local Open Scope pumet_scope.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.

  Global Instance pord_pcomp :
    Proper (pord (T := U -m> V) ==> pord ==> pord) pcomp.
  Proof.
    intros f f' HSubf g g' HSubg x; simpl; rewrite -> HSubf, HSubg; reflexivity.
  Qed.

  Lemma mmcompAL (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ (g ∘ h) ⊑ f ∘ g ∘ h.
  Proof. intros x; reflexivity. Qed.

  Lemma mmcompAR (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ g ∘ h ⊑ f ∘ (g ∘ h).
  Proof. intros x; reflexivity. Qed.

  Global Instance precomp_equiv : Proper (equiv (A := T -m> U) ==> equiv) precomp_mne.
  Proof. resp_set. Qed.

  Global Instance precomp_dist n : Proper (dist n (T := T -m> U) ==> dist n) precomp_mne.
  Proof. resp_set. Qed.

  Global Instance precomp_ord : Proper (pord ==> pord) precomp_mne.
  Proof. mono_resp. Qed.

  Global Instance postcomp_equiv : Proper (equiv (A := T -m> U) ==> equiv) postcomp_mne.
  Proof. resp_set. Qed.

  Global Instance postcomp_dist n : Proper (dist n (T := T -m> U) ==> dist n) postcomp_mne.
  Proof. resp_set. Qed.

  Global Instance postcomp_ord : Proper (pord ==> pord) postcomp_mne.
  Proof. mono_resp. Qed.

  Lemma ucomp_precomp (f : U -m> V) (g : T -m> U) :
    g ▹ ∘ f ▹ == precomp_mne (V := W) (f ∘ g).
  Proof.
    intros h; simpl morph; symmetry; apply pcomp_assoc.
  Qed.

  Lemma pid_precomp :
    precomp_mne (V := U) (pid T) == pid (T -m> U).
  Proof.
    intros f; simpl; apply pcomp_pid_right.
  Qed.

  Lemma ucomp_postcomp (f : T -m> U) (g : V -m> T) :
    ◃ f ∘ ◃ g == postcomp_mne (V := W) (f ∘ g).
  Proof.
    intros h; simpl; apply pcomp_assoc.
  Qed.

  Lemma pid_postcomp :
    postcomp_mne (V := T) (pid U) == pid (T -m> U).
  Proof.
    intros f; simpl; apply pcomp_pid_left.
  Qed.

End MMorphProps2.

Section MonotoneProducts.
  Local Open Scope pumet_scope.
  Context `{pcT : pcmType T} `{pcU : pcmType U} `{pcV : pcmType V}.
  Local Obligation Tactic := intros; apply _ || mono_resp || program_simpl.

  Global Instance pcmType_prod : pcmType (U * V).
  Proof.
    split.
    intros σ ρ σc ρc HC; split; unfold liftc; eapply pcm_respC; try assumption; unfold liftc;
    intros i; rewrite -> HC; reflexivity.
  Qed.

(* RJ These are already in Predom.v, right?
  Global Instance pcmprod_proper : Proper (pord ++> pord ++> pord) (@pair U V).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
  Qed.

  Global Instance pcmfst_proper : Proper (pord ++> pord) (@fst U V).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.

  Global Instance pcmsnd_proper : Proper (pord ++> pord) (@snd U V).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.
*)

  Definition pcmfst : (U * V) -m> U := m[(Mfst)].
  Definition pcmsnd : (U * V) -m> V := m[(Msnd)].

  Program Definition pcmprod (f: T -m> U) (g: T -m> V) : T -m> (U * V) :=
    m[(Mprod f g)].

  Lemma pcmprod_unique (f: T -m> U) (g: T -m> V) (h: T -m> U * V) :
    pcmfst ∘ h == f -> pcmsnd ∘ h == g -> h == pcmprod f g.
  Proof.
    intros HL HR x; split; simpl; [rewrite <- HL | rewrite <- HR]; reflexivity.
  Qed.

End MonotoneProducts.

Notation "〈 f , g 〉" := (pcmprod f g) : pumet_scope.
Notation "'π₁'" := pcmfst : pumet_scope.
Notation "'π₂'" := pcmsnd : pumet_scope.


Section Extras.
  Local Open Scope pumet_scope.
  Local Obligation Tactic := intros; apply _ || mono_resp || program_simpl.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.

  Definition pcmprod_map (f : T -m> U) (g : V -m> W) := 〈f ∘ π₁, g ∘ π₂〉.
    
  Global Instance pcmprod_map_resp : Proper (equiv ==> equiv ==> equiv) pcmprod_map.
  Proof. intros f g H1 h j H2 [t1 v1]; simpl; now rewrite -> H1, H2. Qed.
  
  Global Instance pcmprod_map_nonexp n : Proper (dist n ==> dist n ==> dist n) pcmprod_map.
  Proof.
    intros f g H1 h j H2 [t1 v1]; split; simpl; [ rewrite H1 | rewrite H2]; reflexivity.
  Qed.
  
  Global Instance pcmprod_map_monic : Proper (pord ==> pord ==> pord) pcmprod_map.
  Proof.
    intros f g H1 h j H2 [t1 v1]; split; simpl; [ rewrite -> H1 | rewrite -> H2]; reflexivity.
  Qed.
  
  Program Definition pcmconst u : T -m> U := mkMUMorph (umconst u) _.
  
End Extras.
  
Section Instances.
  Local Open Scope pumet_scope.
  Local Obligation Tactic := intros; apply _ || mono_resp || program_simpl.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.

  Lemma pcmprod_map_id : pcmprod_map (pid T) (pid U) == pid _. 
  Proof. simpl. repeat intro; split; reflexivity. Qed.

  Context `{pX : pcmType Y} `{pY : pcmType X} {f : T -m> U} {g : V -m> W} {h : X -m> T} {j : Y -m> V}.
  
  Lemma pcmprod_map_comp  :
  ((pcmprod_map f g) ∘ (pcmprod_map h j))%pm == (pcmprod_map (f ∘ h) (g ∘ j))%pm.
  Proof. intros [x y]; reflexivity. Qed.
End Instances.

Notation "f × g" := (pcmprod_map f g) (at level 40, left associativity) : pumet_scope.

Section PCMExponentials.
  Local Open Scope pumet_scope.
  Local Obligation Tactic := intros; apply _ || mono_resp || program_simpl.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.

  Program Definition um_bin_morph (f : T -m> U -m> V) : T -n> U -n> V :=
    lift2m (lift2s (fun a b => f a b) _ _) _ _.

  Program Definition pcmuncurry (f : T -m> U -m> V) : T * U -m> V :=
    m[(uncurry (um_bin_morph f))].
  Next Obligation.
    intros [a1 b1] [a2 b2] [HSa HSb]; simpl in *; now rewrite -> HSa, HSb.
  Qed.

  Program Definition lift2_pcm (f : T -n> U -n> V) p q : T -m> U -m> V :=
    mkMUMorph (mkUMorph (mkMorph (fun a => mkMUMorph (f a) (p a)) _) _) q.

  Program Definition mcurry (f : T * U -m> V) : T -m> U -m> V :=
    lift2_pcm (curryM f) _ _.

  Program Definition meval : (T -m> U) * T -m> U :=
    m[(evalM <M< prodM_map n[(mu_morph (U := U))] (umid _))].
  Next Obligation.
    intros [f a] [g b] [Sub1 Sub2]; simpl in *; rewrite -> Sub1, Sub2; reflexivity.
  Qed.

End PCMExponentials.

Section PCMExpProps.
  Local Open Scope pumet_scope.
  Context `{pT : pcmType T} `{pU : pcmType U} `{pV : pcmType V} `{pW : pcmType W}.

  Lemma pcmcurry_com (f : T * U -m> V) : f == meval ∘ (mcurry f × pid _).
  Proof. intros [a b]; reflexivity. Qed.

  Lemma mcurry_uniqe (f : T * U -m> V) h :
    f == meval ∘ (h × pid _) -> mcurry f == h.
  Proof. intros HEq a b; simpl; rewrite HEq; reflexivity. Qed.

End PCMExpProps.

Section SubPCM.
  Local Open Scope pumet_scope.
  Local Obligation Tactic := intros; apply _ || mono_resp || eauto.
  Context `{pcT : pcmType T} `{pcU : pcmType U} {P : T -> Prop} {C : LimitPreserving P}.

  Program Definition p1sNE :=
    n[(fun x : {a : T | P a} => proj1_sig x)].

  Global Instance pcmType_sub : pcmType {a : T | P a}.
  Proof.
    split.
    intros σ ρ σc ρc SUBc; simpl.
    eapply pcm_respC; [assumption |]; intros i; simpl; apply SUBc.
  Qed.

  Global Instance proj1sig_proper :
    Proper (pord (T := {t : T | P t}) ==> pord) (@proj1_sig T P).
  Proof. intros [x Hx] [y Hy] HEq; simpl; apply HEq. Qed.

  Definition muincl : {a : T | P a} -m> T := m[(inclM)].

  Program Definition muinherit (f : U -m> T) (HB : forall b, P (f b)) : U -m> {a : T | P a} :=
    m[(inheritM f HB)].

  Lemma muforget_mono (f g : U -m> {a : T | P a}) : muincl ∘ f ⊑ muincl ∘ g -> f ⊑ g.
  Proof.
    move=> HEq x; exact: HEq.
  Qed.

  Lemma muforget_mono' (f g : U -m> {a : T | P a}) : muincl ∘ f == muincl ∘ g -> f == g.
  Proof.
    move=> HEq x; exact: HEq.
  Qed.

End SubPCM.

(** Extending the pcbult's to option types.

    Caution: this is *one* of the ways to define the order, and not necessarily the only useful.
    Thus, the instances are local, and should be declared w/ Existing Instance where needed. *)
Section Option.
  Context `{pcV : pcmType V}.

  (* The preorder on options where None is the bottom element. *)
  Section Bot.

    Existing Instance option_preo_bot.

    Instance option_pcm_bot : pcmType (option V).
    Proof.
      split.
      - intros σ ρ σc ρc HS.
        unfold compl, option_cmt, option_compl at 1; simpl.
        generalize (@eq_refl _ (σ 1)); pattern (σ 1) at 1 3; destruct (σ 1) as [vs1 |]; intros; [| exact I].
        unfold option_compl; simpl.
        generalize (@eq_refl _ (ρ 1)); pattern (ρ 1) at 1 3; destruct (ρ 1) as [vr1 |]; intros; [| exfalso].
        { eapply pcm_respC; [assumption | intros].
          unfold unSome at 1; simpl.
          generalize (@eq_refl _ (σ (S i))); pattern (σ (S i)) at 1 3; destruct (σ (S i)) as [vsi |]; intros.
          + unfold unSome; simpl.
            generalize (@eq_refl _ (ρ (S i))); pattern (ρ (S i)) at 1 3; destruct (ρ (S i)) as [vri |]; intros.
            * specialize (HS (S i)); rewrite <- e1, <- e2 in HS; apply HS.
            * exfalso; specialize (ρc 1 1 (S i)); rewrite <- e0, <- e2 in ρc; apply ρc; auto with arith.
          + exfalso; specialize (σc 1 1 (S i)); rewrite <- e, <- e1 in σc; apply σc; auto with arith.
        }
        specialize (HS 1); rewrite <- e0, <- e in HS; apply HS.
    Qed.

  End Bot.

  (* And the preorder, where None is a top element *)
  Section Top.

    Existing Instance option_preo_top.

    Instance option_pcm_top : pcmType (option V).
    Proof.
      split.
      - intros σ ρ σc ρc HS.
        unfold compl, option_cmt, option_compl at 2; simpl.
        generalize (@eq_refl _ (ρ 1)); pattern (ρ 1) at 1 3; destruct (ρ 1) as [vr1 |]; intros; [| exact I].
        unfold option_compl; simpl.
        generalize (@eq_refl _ (σ 1)); pattern (σ 1) at 1 3; destruct (σ 1) as [vs1 |]; intros; [| exfalso].
        { unfold pord; simpl.
          eapply pcm_respC; [assumption | intros].
          unfold unSome at 1; simpl.
          generalize (@eq_refl _ (σ (S i))); pattern (σ (S i)) at 1 3; destruct (σ (S i)) as [vsi |]; intros.
          + unfold unSome; simpl.
            generalize (@eq_refl _ (ρ (S i))); pattern (ρ (S i)) at 1 3; destruct (ρ (S i)) as [vri |]; intros.
            * specialize (HS (S i)); rewrite <- e1, <- e2 in HS; apply HS.
            * exfalso; specialize (ρc 1 1 (S i)); rewrite <- e, <- e2 in ρc; apply ρc; auto with arith.
          + exfalso; specialize (σc 1 1 (S i)); rewrite <- e0, <- e1 in σc; apply σc; auto with arith.
        }
        specialize (HS 1); rewrite <- e0, <- e in HS; apply HS.
    Qed.

  End Top.

End Option.

Class extensible V `{pcmV : pcmType V} :=
  mkExtend { extend : V -> V -> V;
             extend_dist n (v vd ve : V) (HD : v = S n = vd) (HS : v ⊑ ve) :
               ve = S n = extend ve vd;
             extend_sub  n (v vd ve : V) (HD : v = S n = vd) (HS : v ⊑ ve) :
               vd ⊑ extend ve vd
           }.
Arguments mkExtend {_ _ _ _ _ _} _ {_ _}.
Arguments extend_dist {_ _ _ _ _ _ _} {_} {_ _ _} _ _.
Arguments extend_sub {_ _ _ _ _ _ _} {_} {_ _ _} _ _.

Section ExtOrdDiscrete.
  Context U `{cmU : cmetric U}.

  Program Instance disc_preo : preoType U := mkPOType equiv _.
  Next Obligation.
    split; apply _.
  Qed.
  Next Obligation.
    move=> x1 x2 Rx y1 y2 Ry.
    by rewrite Rx Ry.
  Qed.

  Instance disc_pcm : pcmType U.
  Proof.
    split; simpl.
    - intros σ ρ σc ρc HS.
      apply umet_complete_ext; assumption.
  Qed.

  Program Instance disc_ext : extensible U := mkExtend (fun ueq ud => ud).
  Next Obligation.
    rewrite <- HS; assumption.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

End ExtOrdDiscrete.

Section ExtMetricDiscrete.
  Context T {eqtT : Setoid T} {preoT : preoType T}.

  Global Instance disc_metric_pcm : pcmType (mT:=discreteMetric) (cmT:=discreteCMetric) T.
  Proof.
    split. move=>σ ρ σc ρc Hle.
    rewrite /compl /= /discreteCompl.
    by apply: Hle.
  Qed.
End ExtMetricDiscrete.


Section ExtProd.
  Context T U `{ET : extensible T} `{EU : extensible U}. 

  Global Instance prod_extensible : extensible (T * U) := mkExtend (fun s s' => pair (extend (fst s) (fst s')) (extend (snd s) (snd s'))).
  Proof. 
    - intros n [v1 v2] [vd1 vd2] [ve1 ve2] [E1 E2] [S1 S2]. 
      split.
      + eapply (extend_dist E1 S1). 
      + eapply (extend_dist E2 S2). 
    - intros n [v1 v2] [vd1 vd2] [ve1 ve2] [E1 E2] [S1 S2]. 
      split.
      + eapply (extend_sub E1 S1).
      + eapply (extend_sub E2 S2).
  Qed.

End ExtProd.
