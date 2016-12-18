From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".
Import uPred.

Class irisG' (Λstate : Type) (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;
  state_interp : Λstate → iProp Σ;
}.
Notation irisG Λ Σ := (irisG' (state Λ) Σ).

Definition wp_pre `{irisG Λ Σ}
    (wp : bool -c> coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ) :
    bool -c> coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ := λ p E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1,
     state_interp σ1 ={E,∅}=∗ ⌜if p then reducible e1 σ1 else True⌝ ∗
     ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
       state_interp σ2 ∗ wp p E e2 Φ ∗
       [∗ list] ef ∈ efs, wp p ⊤ ef (λ _, True)
  end%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre=> n wp wp' Hwp p E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} :
  bool → coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint wp_pre.
Definition wp_aux : seal (@wp_def). by eexists. Qed.
Definition wp := unseal wp_aux.
Definition wp_eq : @wp = @wp_def := seal_eq wp_aux.

Arguments wp {_ _ _} _ _ _%E _.
Instance: Params (@wp) 6.

Notation "'WP' e @ p ; E {{ Φ } }" := (wp p E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  p ;  E  {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e @ E {{ Φ } }" := (wp true E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e @ E ? {{ Φ } }" := (wp false E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e {{ Φ } }" := (wp true ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e ? {{ Φ } }" := (wp false ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' ? {{  Φ  } } ']'") : uPred_scope.

Notation "'WP' e @ p ; E {{ v , Q } }" := (wp p E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  p ;  E  {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp true E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp false E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e {{ v , Q } }" := (wp true ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp false ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' ? {{  v ,  Q  } } ']'") : uPred_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ p ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ p; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  p ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,   RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,   RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ p ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ p; E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  p ;  E  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : uPred_scope.

Notation "'{{{' P } } } e @ p ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ p; E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  p ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ p ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ p; E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  p ;  E  {{{  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : C_scope.

Section wp.
Context `{irisG Λ Σ}.
Implicit Types p : bool.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold p E e Φ : WP e @ p; E {{ Φ }} ⊣⊢ wp_pre wp p E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne p E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@wp Λ Σ _ p E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 17 (f_contractive || f_equiv). apply IH; first lia.
  intros v. eapply dist_le; eauto with omega.
Qed.
Global Instance wp_proper p E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@wp Λ Σ _ p E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' p E Φ v : Φ v ⊢ WP of_val v @ p; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv p E Φ v : WP of_val v @ p; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono p E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP e @ p; E1 {{ Φ }} ⊢ WP e @ p; E2 {{ Ψ }}.
Proof.
  iIntros (?) "[HΦ H]". iLöb as "IH" forall (e). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "($ & H & $)"; auto.
  iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
Qed.

Lemma wp_forget_progress E e Φ : WP e @ E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|]; first iExact "H".
  iIntros (σ1) "Hσ". iMod ("H" with "Hσ") as "[#Hred H]". iModIntro.
  iSplit; first done. iNext. iIntros (e2 σ2 efs) "#Hstep".
  iMod ("H" with "Hstep") as "($ & He2 & Hefs)". iModIntro.
  iSplitL "He2"; first by iApply ("IH" with "He2"). iClear "Hred Hstep".
  induction efs as [|ef efs IH]; first by iApply big_sepL_nil.
  rewrite !big_sepL_cons. iDestruct "Hefs" as "(Hef & Hefs)".
  iSplitL "Hef". by iApply ("IH" with "Hef"). exact: IH. 
Qed.

Lemma fupd_wp p E e Φ : (|={E}=> WP e @ p; E {{ Φ }}) ⊢ WP e @ p; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd p E e Φ : WP e @ p; E {{ v, |={E}=> Φ v }} ⊢ WP e @ p; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono p E); try iFrame; auto. Qed.

Lemma wp_atomic' p E1 E2 e Φ :
  StronglyAtomic e ∨ p ∧ Atomic e →
  (|={E1,E2}=> WP e @ p; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ p; E1 {{ Φ }}.
Proof.
  iIntros (Hatomic) "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|].
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  destruct Hatomic as [Hstrong|[? Hweak]].
  - destruct (Hstrong _ _ _ _ Hstep) as [v <-%of_to_val].
    iMod ("H" with "[#]") as "($ & H & $)"; first done.
    iMod (wp_value_inv with "H") as ">H". by iApply wp_value'.
  - destruct p; last done. iMod ("H" with "[//]") as "(Hphy & H & $)".
    rewrite !wp_unfold /wp_pre. destruct (to_val e2).
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" with "[$]") as "[H _]".
      iDestruct "H" as %(? & ? & ? & ?). by edestruct (Hweak _ _ _ _ Hstep).
Qed.

Lemma wp_step_fupd p E1 E2 e P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ p; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ p; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1) "Hσ". iMod "HR". iMod ("H" with "[$]") as "[$ H]".
  iModIntro; iNext; iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! e2 σ2 efs with "[% //]") as "($ & H & $)".
  iMod "HR". iModIntro. iApply (wp_strong_mono p E2); first done.
  iSplitR "H"; last iExact "H". iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx Λ K} p E e Φ :
  WP e @ p; E {{ v, WP K (of_val v) @ p; E {{ Φ }} }} ⊢ WP K e @ p; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct p; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iNext; iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "($ & H & $)".
  by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx Λ K} p E e Φ :
  WP K e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, WP K (of_val v) @ p; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { destruct p; eauto using reducible_fill. }
  iNext; iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! (K e2) σ2 efs with "[]") as "($ & H & $)"; eauto using fill_step.
  by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono p E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono p E E); auto.
  iIntros "{$H}" (v) "?". by iApply HΦ.
Qed.
Lemma wp_mask_mono p E1 E2 e Φ : E1 ⊆ E2 → WP e @ p; E1 {{ Φ }} ⊢ WP e @ p; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono p E1 E2); auto. iFrame; eauto. Qed.
Global Instance wp_mono' p E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@wp Λ Σ _ p E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value p E Φ e v `{!IntoVal e v} : Φ v ⊢ WP e @ p; E {{ Φ }}.
Proof. intros; rewrite -(of_to_val e v) //; by apply wp_value'. Qed.
Lemma wp_value_fupd' p E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ p; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd p E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ p; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.

Lemma wp_strong_atomic p E1 E2 e Φ :
  StronglyAtomic e →
  (|={E1,E2}=> WP e @ p; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ p; E1 {{ Φ }}.
Proof. by eauto using wp_atomic'. Qed.
Lemma wp_atomic E1 E2 e Φ :
  Atomic e →
  (|={E1,E2}=> WP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }}.
Proof. by eauto using wp_atomic'. Qed.

Lemma wp_frame_l p E e Φ R : R ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[??]". iApply (wp_strong_mono p E E _ Φ); try iFrame; eauto. Qed.
Lemma wp_frame_r p E e Φ R : WP e @ p; E {{ Φ }} ∗ R ⊢ WP e @ p; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[??]". iApply (wp_strong_mono p E E _ Φ); try iFrame; eauto. Qed.

Lemma wp_frame_step_l p E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ p; E2 {{ Φ }} ⊢ WP e @ p; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r p E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ p; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ p; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' p E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l p E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' p E e Φ R :
  to_val e = None → WP e @ p; E {{ Φ }} ∗ ▷ R ⊢ WP e @ p; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r p E E); try iFrame; eauto. Qed.

Lemma wp_wand p E e Φ Ψ :
  WP e @ p; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ p; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono p E); auto.
  iIntros "{$Hwp}" (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l p E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ p; E {{ Φ }} ⊢ WP e @ p; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r p E e Φ Ψ :
  WP e @ p; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ p; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p p' E e R Φ Ψ :
    (∀ v, Frame p' R (Φ v) (Ψ v)) → Frame p' R (WP e @ p; E {{ Φ }}) (WP e @ p; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp p E e Φ : IsExcept0 (WP e @ p; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ :
    ElimModal (|==> P) P (WP e @ p; E {{ Φ }}) (WP e @ p; E {{ Φ }}).
  Proof. by rewrite /ElimModal (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ :
    ElimModal (|={E}=> P) P (WP e @ p; E {{ Φ }}) (WP e @ p; E {{ Φ }}).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  (* lower precedence, if possible, it should persistently pick elim_upd_fupd_wp *)
  Global Instance elim_modal_fupd_wp_strong_atomic E1 E2 e P Φ :
    StronglyAtomic e →
    ElimModal (|={E1,E2}=> P) P
            (WP e @ p; E1 {{ Φ }}) (WP e @ p; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_strong_atomic. Qed.

  (* lower precedence than elim_modal_fupd_wp_strong_atomic (for no good reason) *)
  Global Instance elim_modal_fupd_wp_atomic E1 E2 e P Φ :
    Atomic e →
    ElimModal (|={E1,E2}=> P) P
            (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 110.
  Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_atomic. Qed.
End proofmode_classes.
