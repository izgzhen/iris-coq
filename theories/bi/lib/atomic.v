From iris.bi Require Export bi updates.
From stdpp Require Import coPset.
From iris.proofmode Require Import classes class_instances.
Set Default Proof Using "Type".

Definition atomic_shift {PROP: sbi} `{!FUpd PROP} {A B : Type}
  (α: A → PROP) (* atomic pre-condition *)
  (β: A → B → PROP) (* atomic post-condition *)
  (Ei Eo: coPset) (* inside/outside masks *)
  (Q: A → B → PROP) (* post-condition *)
  : PROP :=
    (∃ (F P:PROP), F ∗ ▷ P ∗ □ (▷ P ={Eo, Ei}=∗ ∃ x, α x ∗
          ((α x ={Ei, Eo}=∗ ▷ P) ∧ (∀ y, β x y ={Ei, Eo}=∗ F -∗ Q x y)))
    )%I.
