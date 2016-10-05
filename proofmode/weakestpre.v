From iris.proofmode Require Export classes pviewshifts.
From iris.proofmode Require Import coq_tactics.
From iris.program_logic Require Export weakestpre.
Import uPred.

Section weakestpre.
Context `{irisG Λ Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Global Instance frame_wp E e R Φ Ψ :
  (∀ v, Frame R (Φ v) (Ψ v)) → Frame R (WP e @ E {{ Φ }}) (WP e @ E {{ Ψ }}).
Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

Global Instance is_except_last_wp E e Φ : IsExceptLast (WP e @ E {{ Φ }}).
Proof. by rewrite /IsExceptLast -{2}pvs_wp -except_last_pvs -pvs_intro. Qed.

Global Instance elim_vs_rvs_wp E e P Φ :
  ElimVs (|=r=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}) | 2.
Proof. by rewrite /ElimVs (rvs_pvs E) pvs_frame_r wand_elim_r pvs_wp. Qed.

Global Instance elim_vs_pvs_wp E e P Φ :
  ElimVs (|={E}=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}) | 1.
Proof. by rewrite /ElimVs pvs_frame_r wand_elim_r pvs_wp. Qed.

(* lower precedence, if possible, it should always pick elim_vs_pvs_wp *)
Global Instance elim_vs_pvs_wp_atomic E1 E2 e P Φ :
  atomic e →
  ElimVs (|={E1,E2}=> P) P
         (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
Proof. intros. by rewrite /ElimVs pvs_frame_r wand_elim_r wp_atomic. Qed.
End weakestpre.
