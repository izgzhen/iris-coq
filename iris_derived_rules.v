Require Import ssreflect.
Require Import world_prop core_lang lang masks iris_core iris_plog iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_DERIVED_RULES (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG).
  Export VS_RULES.
  Export HT_RULES.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (* Ideally, these rules should never talk about worlds or such.
     At the very least, they should not open the definition of the complex assertrtions:
     invariants, primitive view shifts, weakest pre. *)

  Section DerivedVSRules.

    Implicit Types (P : Props) (i : nat) (m : mask) (e : expr) (r : res).

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      rewrite ->valid_iff, box_top.
      unfold vs; apply box_intro.
      rewrite <- and_impl, and_projR.
      apply bot_false.
    Qed.

    Lemma vsNotOwnInvalid m1 m2 r
       (Hnval: ~↓r):
      valid (vs m1 m2 (ownR r) ⊥).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsNotOwnInvalid; eassumption.
    Qed.

    Lemma vsTimeless m P :
      timeless P ⊑ vs m m (▹P) P.
    Proof.
      move=>w0 n0 r0 Htl w1 Hw01 n1 r1 Hn01 _ HP.
      eapply pvsTimeless. split; last assumption.
      eapply propsMWN, Htl; eassumption.
    Qed.

    Lemma vsTrans P Q R m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 P Q ∧ vs m2 m3 Q R ⊑ vs m1 m3 P R.
    Proof.
      move=> w0 n0 r0 [HPQ HQR] w1 HSub n1 r1 Hlt _ HP.
      eapply pvsTrans; first by eauto.
      eapply pvsImpl; split; first eapply propsMWN; 
      [eassumption | eassumption | exact HQR | ].
      eapply HPQ; by eauto using unit_min.
    Qed.

    Lemma vsEnt P Q m :
      □(P → Q) ⊑ vs m m P Q.
    Proof.
      move => w0 n r0 HPQ w1 HSub n1 r1 Hlt _ /(HPQ _ HSub _ _ Hlt) HQ.
      eapply pvsEnt, HQ; exact unit_min.
    Qed.

    Existing Instance LP_res.

    Lemma vsGhostUpd m rl (P : RL.res -> Prop) (HU : rl ⇝∈ P) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsGhostUpd, Hown. assumption.
    Qed.

    Lemma vsGhostStep m (rl rl': RL.res) (HU : rl ⇝ rl') :
      valid (vs m m (ownL rl) (ownL rl')).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsGhostStep, Hown. assumption.
    Qed.

    Lemma vsOpen i P :
      valid (vs (mask_sing i) mask_emp (inv i P) (▹P)).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hinv.
      eapply pvsOpen, Hinv.
    Qed.

    Lemma vsClose i P :
      valid (vs mask_emp (mask_sing i) (inv i P ∧ ▹P) ⊤).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hpre.
      eapply pvsClose, Hpre.
    Qed.

    Existing Instance LP_mask.

    Lemma vsNewInv P m (HInf : mask_infinite m) :
      valid (vs m m (▹P) (xist (inv' m P))).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ HP.
      eapply pvsNewInv; eassumption.
    Qed.

  End DerivedVSRules. 

End IRIS_DERIVED_RULES.

Module IrisDerivedRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG) : IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
  Include IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
End IrisDerivedRules.
