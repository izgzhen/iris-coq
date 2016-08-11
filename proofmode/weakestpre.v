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

Global Instance to_assert_wp E e P Φ :
  IntoAssert P (WP e @ E {{ Ψ }}) (|={E}=> P).
Proof. intros. by rewrite /IntoAssert pvs_frame_r wand_elim_r pvs_wp. Qed.

Global Instance is_except_now_wp E e Φ : IsNowTrue (WP e @ E {{ Φ }}).
Proof. by rewrite /IsNowTrue -{2}pvs_wp -except_now_pvs -pvs_intro. Qed.

Global Instance elim_shift_shift_wp E e P Φ :
  ElimShift (|=r=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
Proof. by rewrite /ElimShift (shift_pvs E) pvs_frame_r wand_elim_r pvs_wp. Qed.

Global Instance elim_shift_pvs_wp E e P Φ :
  ElimShift (|={E}=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
Proof. by rewrite /ElimShift pvs_frame_r wand_elim_r pvs_wp. Qed.

(* lower precedence, if possible, it should always pick elim_shift_pvs_wp *)
Global Instance elim_shift_pvs_wp_atomic E1 E2 e P Φ :
  atomic e →
  ElimShift (|={E1,E2}=> P) P
         (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
Proof. intros. by rewrite /ElimShift pvs_frame_r wand_elim_r wp_atomic. Qed.
End weakestpre.
