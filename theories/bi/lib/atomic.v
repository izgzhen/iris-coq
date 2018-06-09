From iris.bi Require Export bi updates laterable.
From iris.bi.lib Require Import fixpoint.
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import coq_tactics tactics reduction.
Set Default Proof Using "Type".

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  (** atomic_acc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  Definition atomic_acc Eo Ei α P β Φ : PROP :=
    (|={Eo, Ei}=> ∃.. x, α x ∗
          ((α x ={Ei, Eo}=∗ P) ∧ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))
    )%I.

  Lemma atomic_acc_wand Eo Ei α P1 P2 β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀.. x y, Φ1 x y -∗ Φ2 x y)) -∗
    (atomic_acc Eo Ei α P1 β Φ1 -∗ atomic_acc Eo Ei α P2 β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma atomic_acc_mask Eo Ed α P β Φ :
    atomic_acc Eo (Eo∖Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic_acc E (E∖Ed) α P β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done.
    - iIntros (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  Lemma atomic_acc_mask_weaken Eo1 Eo2 Ei α P β Φ :
    Eo1 ⊆ Eo2 →
    atomic_acc Eo1 Ei α P β Φ -∗ atomic_acc Eo2 Ei α P β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod fupd_intro_mask' as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iSplitWith "Hclose2".
    - iIntros "Hα". iMod ("Hclose2" with "Hα") as "$". done.
    - iIntros (y) "Hβ". iMod ("Hclose2" with "Hβ") as "$". done.
  Qed.

  (** atomic_update as a fixed-point of the equation
   AU = ∃ P. ▷ P ∗ □ (▷ P ==∗ α ∗ (α ==∗ AU) ∧ (β ==∗ Q))
      = ∃ P. ▷ P ∗ □ (▷ P -∗ atomic_acc α AU β Q)
  *)
  Context Eo Ei α β Φ.

  Definition atomic_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    (∃ (P : PROP), ▷ P ∗
     □ (▷ P -∗ atomic_acc Eo Ei α (Ψ ()) β Φ))%I.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2) "#HP12". iIntros ([]) "AU".
      iDestruct "AU" as (P) "[HP #AS]". iExists P. iFrame.
      iIntros "!# HP". iApply (atomic_acc_wand with "[HP12]"); last by iApply "AS".
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Definition atomic_update_def :=
    bi_greatest_fixpoint atomic_update_pre ().

End definition.

(** Seal it *)
Definition atomic_update_aux : seal (@atomic_update_def). by eexists. Qed.
Definition atomic_update `{BiFUpd PROP} {TA TB : tele} := atomic_update_aux.(unseal) PROP _ TA TB.
Definition atomic_update_eq :
  @atomic_update = @atomic_update_def := atomic_update_aux.(seal_eq).

Arguments atomic_acc {PROP _ TA TB} Eo Ei _ _ _ _ : simpl never.
Arguments atomic_update {PROP _ TA TB} Eo Ei _ _ _ : simpl never.

(** Notation: Atomic updates *)
Notation "'AU' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'AU'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AU'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, β%I) ..))
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[   ' 'AU'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleO) (TB:=TeleO) Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AU'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'AACC' '<<' ∀ x1 .. xn , α 'ABORT' P '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn,
                      tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                      (λ y1, .. (λ yn, β%I) .. )
                     ) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn,
                      tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                      (λ y1, .. (λ yn, Φ%I) .. )
                     ) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[     ' 'AACC'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC' '<<' ∀ x1 .. xn , α 'ABORT' P '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder,
   format "'[     ' 'AACC'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC' '<<' α 'ABORT' P '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
              P%I
              (tele_app (TT:=TeleO) $
                        tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                        (λ y1, .. (λ yn, β%I) ..))
              (tele_app (TT:=TeleO) $
                        tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                        (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, y1 binder, yn binder,
   format "'[     ' 'AACC'  '[   ' '<<'  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC' '<<' α 'ABORT' P '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleO)
              (TB:=TeleO)
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
              P%I
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200,
   format "'[     ' 'AACC'  '[   ' '<<'  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Local Existing Instance atomic_update_pre_mono.

  Global Instance atomic_acc_ne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        dist n ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance atomic_update_ne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic_update_eq /atomic_update_def /atomic_update_pre. solve_proper.
  Qed.

  (** The ellimination form: an atomic accessor *)
  Lemma aupd_aacc  Eo Ei α β Φ :
    atomic_update Eo Ei α β Φ -∗
    atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ) β Φ.
  Proof using Type*.
    rewrite atomic_update_eq {1}/atomic_update_def /=. iIntros "HUpd".
    iPoseProof (greatest_fixpoint_unfold_1 with "HUpd") as "HUpd".
    iDestruct "HUpd" as (P) "(HP & Hshift)". by iApply "Hshift".
  Qed.

  Global Instance aupd_laterable Eo Ei α β Φ :
    Laterable (atomic_update Eo Ei α β Φ).
  Proof.
    rewrite /Laterable atomic_update_eq {1}/atomic_update_def /=. iIntros "AU".
    iPoseProof (greatest_fixpoint_unfold_1 with "AU") as (P) "[HP #AS]".
    iExists P. iFrame. iIntros "!# HP !>".
    iApply greatest_fixpoint_unfold_2. iExists P. iFrame "#∗".
  Qed.

  Lemma aupd_intro P Q α β Eo Ei Φ :
    Affine P → Persistent P → Laterable Q →
    (P ∗ Q -∗ atomic_acc Eo Ei α Q β Φ) →
    P ∗ Q -∗ atomic_update Eo Ei α β Φ.
  Proof.
    rewrite atomic_update_eq {1}/atomic_update_def /=.
    iIntros (??? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coind _ (λ _, Q)); last done. iIntros "!#" ([]) "HQ".
    iDestruct (laterable with "HQ") as (Q') "[HQ' #HQi]". iExists Q'. iFrame.
    iIntros "!# HQ'". iDestruct ("HQi" with "HQ'") as ">HQ {HQi}".
    iApply HAU. by iFrame.
  Qed.

  Lemma aacc_intro Eo Ei α P β Φ :
    Ei ⊆ Eo → (∀.. x, α x -∗
    ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗
    atomic_acc Eo Ei α P β Φ)%I.
  Proof.
    iIntros (? x) "Hα Hclose".
    iMod fupd_intro_mask' as "Hclose'"; last iModIntro; first set_solver.
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  Global Instance elim_acc_aacc {X} E1 E2 Ei (α' β' : X → PROP) γ' α β Pas Φ :
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (atomic_acc E1 Ei α Pas β Φ)
            (λ x', atomic_acc E2 Ei α (β' x' ∗ (γ' x' -∗? Pas))%I β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y))
            )%I.
  Proof.
    rewrite /ElimAcc.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iMod (fupd_intro_mask') as "Hclose''"; last iModIntro; first done.
    iExists x. iFrame. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros (y) "Hβ". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hβ") as "Hβ'".
      rewrite ->!tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  Lemma aacc_aacc {TA' TB' : tele} E1 E1' E2 E3
        α P β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_acc E1' E2 α P β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (P ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (P ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (atomic_acc_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplit.
    - iIntros "Hα'". iDestruct "Hclose'" as "[Hclose' _]".
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". auto.
    - iIntros (y') "Hβ'". iDestruct "Hclose'" as "[_ Hclose']".
      iMod ("Hclose'" with "Hβ'") as "Hres".
      rewrite ->!tele_app_bind. iDestruct "Hres" as "[[Hα HΦ']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP".
        iApply "HΦ'". done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct "Hcont" as (y) "[Hβ HΦ']".
        iMod ("Hclose" with "Hβ") as "HΦ".
        iApply "HΦ'". done.
  Qed.

  Lemma aacc_aupd {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aacc with "[Hupd] Hstep"); first done.
    iApply aupd_aacc; done.
  Qed.

  Lemma aacc_aupd_commit {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iRight.
  Qed.

  Lemma aacc_aupd_abort {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', α x ∗ (atomic_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iLeft.
  Qed.

End lemmas.

(** ProofMode support for atomic updates *)
Section proof_mode.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Lemma tac_aupd_intro Γp Γs n α β Eo Ei Φ P :
    Timeless (PROP:=PROP) emp →
    TCForall Laterable (env_to_list Γs) →
    P = prop_of_env Γs →
    envs_entails (Envs Γp Γs n) (atomic_acc Eo Ei α P β Φ) →
    envs_entails (Envs Γp Γs n) (atomic_update Eo Ei α β Φ).
  Proof.
    intros ? HΓs ->. rewrite envs_entails_eq of_envs_eq' /atomic_acc /=.
    setoid_rewrite prop_of_env_sound =>HAU.
    apply aupd_intro; [apply _..|]. done.
  Qed.
End proof_mode.

(** Now the coq-level tactics *)

Tactic Notation "iAuIntro" :=
  iStartProof; eapply tac_aupd_intro; [
    iSolveTC || fail "iAuIntro: emp is not timeless"
  | iSolveTC || fail "iAuIntro: not all spatial assumptions are laterable"
  | (* P = ...: make the P pretty *) pm_reflexivity
  | (* the new proof mode goal *) ].
