From algebra Require Export sts.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

Class StsInG Λ Σ (i : gid) {A B} (R : relation A) (tok : A → set B) := {
  sts_inG :> InG Λ Σ i (stsRA R tok);
}.

Section definitions.
  Context {Λ Σ A B} (i : gid) (R : relation A) (tok : A → set B)
          `{!StsInG Λ Σ i R tok} (γ : gname).
  Definition sts_inv  (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ s, own i γ (sts_auth R tok s set_all) ★ φ s)%I.
  Definition sts_states (S : set A) (T: set B) : iPropG Λ Σ :=
    (■ sts.closed R tok S T ∧ own i γ (sts_frag R tok S T))%I.
  Definition sts_state (s : A) (T: set B) : iPropG Λ Σ :=
    own i γ (sts_frag R tok (sts.up R tok s T) T).
  Definition sts_ctx (N : namespace) (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (sts_inv φ).
End definitions.
Instance: Params (@sts_inv) 9.
Instance: Params (@sts_states) 9.
Instance: Params (@sts_ctx) 10.

Section sts.
  Context `{StsInG Λ Σ StsI (A:=A) R tok}.
  Context (φ : A → iPropG Λ Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types γ : gname.

End sts.
