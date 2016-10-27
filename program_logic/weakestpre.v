From iris.program_logic Require Export fancy_updates language.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics classes.
From iris.algebra Require Import auth.
Import uPred.

Class irisG' (Λstate : Type) (Σ : gFunctors) : Set := IrisG {
  iris_invG :> invG Σ;
  state_inG :> inG Σ (authR (optionUR (exclR (leibnizC Λstate))));
  state_name : gname;
}.
Notation irisG Λ Σ := (irisG' (state Λ) Σ).

Definition ownP `{irisG' Λstate Σ} (σ : Λstate) : iProp Σ :=
  own state_name (◯ (Excl' σ)).
Typeclasses Opaque ownP.
Instance: Params (@ownP) 3.

Definition ownP_auth `{irisG' Λstate Σ} (σ : Λstate) : iProp Σ :=
  own state_name (● (Excl' (σ:leibnizC Λstate))).
Typeclasses Opaque ownP_auth.
Instance: Params (@ownP_auth) 4.

Definition wp_pre `{irisG Λ Σ}
    (wp : coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ) :
    coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ := λ E e1 Φ, (
  (* value case *)
  (∃ v, to_val e1 = Some v ∧ |={E}=> Φ v) ∨
  (* step case *)
  (to_val e1 = None ∧ ∀ σ1,
     ownP_auth σ1 ={E,∅}=★ ■ reducible e1 σ1 ★
     ▷ ∀ e2 σ2 efs, ■ prim_step e1 σ1 e2 σ2 efs ={∅,E}=★
       ownP_auth σ2 ★ wp E e2 Φ ★
       [★ list] ef ∈ efs, wp ⊤ ef (λ _, True)))%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  apply or_ne, and_ne, forall_ne; auto=> σ1; apply wand_ne; auto.
  apply fupd_ne, sep_ne, later_contractive; auto=> i ?.
  apply forall_ne=> e2; apply forall_ne=> σ2; apply forall_ne=> efs.
  apply wand_ne, fupd_ne, sep_ne, sep_ne; auto; first by apply Hwp.
  apply big_opL_ne=> ? ef. by apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint wp_pre.
Definition wp_aux : { x | x = @wp_def }. by eexists. Qed.
Definition wp := proj1_sig wp_aux.
Definition wp_eq : @wp = @wp_def := proj2_sig wp_aux.

Arguments wp {_ _ _} _ _%E _.
Instance: Params (@wp) 5.

Notation "'WP' e @ E {{ Φ } }" := (wp E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "'WP' e {{ Φ } }" := (wp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  {{  Φ  } }") : uPred_scope.

Notation "'WP' e @ E {{ v , Q } }" := (wp E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  @  E  {{  v ,  Q  } }") : uPred_scope.
Notation "'WP' e {{ v , Q } }" := (wp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  {{  v ,  Q  } }") : uPred_scope.

(* Texan triples *)
Notation "'{{{' P } } } e {{{ x .. y ; pat , Q } } }" :=
  (□ ∀ Φ,
      P ★ ▷ (∀ x, .. (∀ y, Q -★ Φ pat%V) .. ) -★ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{ x .. y ;  pat ,  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y ; pat , Q } } }" :=
  (□ ∀ Φ,
      P ★ ▷ (∀ x, .. (∀ y, Q -★ Φ pat%V) .. ) -★ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{ x .. y ;  pat ,  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ ; pat , Q } } }" :=
  (□ ∀ Φ, P ★ ▷ (Q -★ Φ pat%V) -★ WP e {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  {{{ ; pat ,  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ ; pat , Q } } }" :=
  (□ ∀ Φ, P ★ ▷ (Q -★ Φ pat%V) -★ WP e @ E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{ ; pat ,  Q } } }") : uPred_scope.

Notation "'{{{' P } } } e {{{ x .. y ; pat , Q } } }" :=
  (∀ Φ : _ → uPred _,
      P ★ ▷ (∀ x, .. (∀ y, Q -★ Φ pat%V) .. ) ⊢ WP e {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{ x .. y ;  pat ,  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y ; pat , Q } } }" :=
  (∀ Φ : _ → uPred _,
      P ★ ▷ (∀ x, .. (∀ y, Q -★ Φ pat%V) .. ) ⊢ WP e @ E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{ x .. y ;  pat ,  Q } } }") : C_scope.
Notation "'{{{' P } } } e {{{ ; pat , Q } } }" :=
  (∀ Φ : _ → uPred _, P ★ ▷ (Q -★ Φ pat%V) ⊢ WP e {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  {{{ ; pat ,  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ ; pat , Q } } }" :=
  (∀ Φ : _ → uPred _, P ★ ▷ (Q -★ Φ pat%V) ⊢ WP e @ E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{ ; pat ,  Q } } }") : C_scope.

Section wp.
Context `{irisG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Physical state *)
Lemma ownP_twice σ1 σ2 : ownP σ1 ★ ownP σ2 ⊢ False.
Proof. rewrite /ownP own_valid_2. by iIntros (?). Qed.
Global Instance ownP_timeless σ : TimelessP (@ownP (state Λ) Σ _ σ).
Proof. rewrite /ownP; apply _. Qed.

Lemma ownP_agree σ1 σ2 : ownP_auth σ1 ★ ownP σ2 ⊢ σ1 = σ2.
Proof.
  rewrite /ownP /ownP_auth own_valid_2 -auth_both_op.
  by iIntros ([[[] [=]%leibniz_equiv] _]%auth_valid_discrete).
Qed.
Lemma ownP_update σ1 σ2 : ownP_auth σ1 ★ ownP σ1 ==★ ownP_auth σ2 ★ ownP σ2.
Proof.
  rewrite /ownP -!own_op.
  by apply own_update, auth_update, option_local_update, exclusive_local_update.
Qed.

(* Weakest pre *)
Lemma wp_unfold E e Φ : WP e @ E {{ Φ }} ⊣⊢ wp_pre wp E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@wp Λ Σ _ E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre. apply or_ne, and_ne; auto; first solve_proper.
  apply forall_ne=> σ1.
  apply wand_ne, fupd_ne, sep_ne, later_contractive; auto=> i ?.
  apply forall_ne=> e2; apply forall_ne=> σ2; apply forall_ne=> ef.
  apply wand_ne, fupd_ne, sep_ne, sep_ne; auto.
  apply IH; [done|]=> v. eapply dist_le; eauto with omega.
Qed.
Global Instance wp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@wp Λ Σ _ E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' E Φ v : Φ v ⊢ WP of_val v @ E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite wp_unfold /wp_pre.
  iLeft; iExists v; rewrite to_of_val; auto.
Qed.
Lemma wp_value_inv E Φ v : WP of_val v @ E {{ Φ }} ={E}=★ Φ v.
Proof.
  rewrite wp_unfold /wp_pre to_of_val. iIntros "[H|[% _]]"; [|done].
  by iDestruct "H" as (v') "[% ?]"; simplify_eq.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v, Φ v ={E2}=★ Ψ v) ★ WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "[HΦ H]". iLöb as "IH" forall (e). rewrite !wp_unfold /wp_pre.
  iDestruct "H" as "[Hv|[% H]]"; [iLeft|iRight].
  { iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done.
    iApply ("HΦ" with ">[-]"). by iApply (fupd_mask_mono E1 _). }
  iSplit; [done|]; iIntros (σ1) "Hσ".
  iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! _ σ2 efs with "[#]") as "($ & H & $)"; auto.
  iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
Qed.

Lemma fupd_wp E e Φ : (|={E}=> WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { iLeft. iExists v; iSplit; first done.
    by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. }
  iRight; iSplit; [done|]; iIntros (σ1) "Hσ1".
  iMod "H" as "[H|[% H]]"; last by iApply "H".
  iDestruct "H" as (v') "[% ?]"; simplify_eq.
Qed.
Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed.

Lemma wp_atomic E1 E2 e Φ :
  atomic e →
  (|={E1,E2}=> WP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }}.
Proof.
  iIntros (Hatomic) "H". destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply wp_fupd. iApply wp_value'.
    iMod "H". by iMod (wp_value_inv with "H"). }
  setoid_rewrite wp_unfold; rewrite /wp_pre. iRight; iSplit; auto.
  iIntros (σ1) "Hσ". iMod "H" as "[H|[_ H]]".
  { iDestruct "H" as (v') "[% ?]"; simplify_eq. }
  iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  destruct (Hatomic _ _ _ _ Hstep) as [v <-%of_to_val].
  iMod ("H" $! _ σ2 efs with "[#]") as "($ & H & $)"; auto.
  iMod (wp_value_inv with "H") as ">H". by iApply wp_value'.
Qed.

Lemma wp_frame_step_l E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ★ WP e @ E2 {{ Φ }} ⊢ WP e @ E1 {{ v, R ★ Φ v }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (??) "[HR [Hv|[_ H]]]".
  { iDestruct "Hv" as (v) "[% Hv]"; simplify_eq. }
  iRight; iSplit; [done|]. iIntros (σ1) "Hσ".
  iMod "HR". iMod ("H" $! _ with "Hσ") as "[$ H]".
  iModIntro; iNext; iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! e2 σ2 efs with "[%]") as "($ & H & $)"; auto.
  iMod "HR". iModIntro. iApply (wp_strong_mono E2 _ _ Φ); try iFrame; eauto.
Qed.

Lemma wp_bind K `{!LanguageCtx Λ K} E e Φ :
  WP e @ E {{ v, WP K (of_val v) @ E {{ Φ }} }} ⊢ WP K e @ E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  iDestruct "H" as "[Hv|[% H]]".
  { iDestruct "Hv" as (v) "[Hev Hv]"; iDestruct "Hev" as % <-%of_to_val.
    by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre. iRight; iSplit; eauto using fill_not_val.
  iIntros (σ1) "Hσ". iMod ("H" $! _ with "Hσ") as "[% H]".
  iModIntro; iSplit.
  { iPureIntro. unfold reducible in *. naive_solver eauto using fill_step. }
  iNext; iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[%]") as "($ & H & $)"; auto.
  by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono E E); auto.
  iFrame. iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_mask_mono E1 E2 e Φ : E1 ⊆ E2 → WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono E1 E2); auto. iFrame; eauto. Qed.
Global Instance wp_mono' E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@wp Λ Σ _ E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value E Φ e v : to_val e = Some v → Φ v ⊢ WP e @ E {{ Φ }}.
Proof. intros; rewrite -(of_to_val e v) //; by apply wp_value'. Qed.
Lemma wp_value_fupd' E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd E Φ e v :
  to_val e = Some v → (|={E}=> Φ v) ⊢ WP e @ E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.

Lemma wp_frame_l E e Φ R : R ★ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ★ Φ v }}.
Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.
Lemma wp_frame_r E e Φ R : WP e @ E {{ Φ }} ★ R ⊢ WP e @ E {{ v, Φ v ★ R }}.
Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.

Lemma wp_frame_step_r E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ E2 {{ Φ }} ★ (|={E1,E2}▷=> R) ⊢ WP e @ E1 {{ v, Φ v ★ R }}.
Proof.
  rewrite [(WP _ @ _ {{ _ }} ★ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' E e Φ R :
  to_val e = None → ▷ R ★ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ★ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' E e Φ R :
  to_val e = None → WP e @ E {{ Φ }} ★ ▷ R ⊢ WP e @ E {{ v, Φ v ★ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto. Qed.

Lemma wp_wand_l E e Φ Ψ :
  (∀ v, Φ v -★ Ψ v) ★ WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
Proof.
  iIntros "[H Hwp]". iApply (wp_strong_mono E); auto.
  iFrame "Hwp". iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_r E e Φ Ψ :
  WP e @ E {{ Φ }} ★ (∀ v, Φ v -★ Ψ v) ⊢ WP e @ E {{ Ψ }}.
Proof. by rewrite comm wp_wand_l. Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp E e R Φ Ψ :
    (∀ v, Frame R (Φ v) (Ψ v)) → Frame R (WP e @ E {{ Φ }}) (WP e @ E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp E e Φ : IsExcept0 (WP e @ E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp E e P Φ :
    ElimModal (|==> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof. by rewrite /ElimModal (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_modal_fupd_wp E e P Φ :
    ElimModal (|={E}=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  (* lower precedence, if possible, it should always pick elim_upd_fupd_wp *)
  Global Instance elim_modal_fupd_wp_atomic E1 E2 e P Φ :
    atomic e →
    ElimModal (|={E1,E2}=> P) P
            (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_atomic. Qed.
End proofmode_classes.
