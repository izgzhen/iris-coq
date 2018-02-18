From iris.bi Require Export bi updates.
From stdpp Require Import coPset.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition atomic_shift {PROP: sbi} `{!FUpd PROP} {A B : Type}
  (α : A → PROP) (* atomic pre-condition *)
  (β : A → B → PROP) (* atomic post-condition *)
  (Eo Em : coPset) (* outside/module masks *)
  (P : PROP) (* pre-condition *)
  (Q : A → B → PROP) (* post-condition *)
  : PROP :=
    (□ (∀ E, ⌜Eo ⊆ E⌝ -∗ ▷ P ={E, E∖Em}=∗ ∃ x, α x ∗
          ((α x ={E∖Em, E}=∗ ▷ P) ∧ (∀ y, β x y ={E∖Em, E}=∗ Q x y)))
    )%I.

Definition atomic_update {PROP: sbi} `{!FUpd PROP} {A B : Type}
  (α : A → PROP) (* atomic pre-condition *)
  (β : A → B → PROP) (* atomic post-condition *)
  (Eo Em : coPset) (* outside/module masks *)
  (Q : A → B → PROP) (* post-condition *)
  : PROP :=
    tc_opaque (
      ∃ (F P : PROP), F ∗ ▷ P ∗ atomic_shift α β Eo Em P (λ x y, F -∗ Q x y)
    )%I.

Section lemmas.
  Context {PROP: sbi} `{FUpdFacts PROP} {A B : Type}.
  Implicit Types (α : A → PROP) (β: A → B → PROP) (P : PROP) (Q : A → B → PROP).

  Lemma aupd_acc α β Eo Em Q E :
    Eo ⊆ E →
    atomic_update α β Eo Em Q -∗
    |={E, E∖Em}=> ∃ x, α x ∗
      ((α x ={E∖Em, E}=∗ atomic_update α β Eo Em Q) ∧
       (∀ y, β x y ={E∖Em, E}=∗ Q x y)).
  Proof using Type*.
    rewrite {1}/atomic_update /=. iIntros (HE) "HUpd".
    iDestruct "HUpd" as (F P) "(HF & HP & #Hshift)".
    iMod ("Hshift" with "[% //] HP") as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iModIntro. iExists F, P.
      by iFrame.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iMod ("Hclose" with "Hβ") as "HQ". iModIntro. by iApply "HQ".
  Qed.
End lemmas.
