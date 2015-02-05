Set Automatic Coercions Import.
Require Import ssreflect ssrfun ssrbool eqtype seq fintype.
Require Import core_lang masks iris_wp.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************)
(** * Rules for unsafe triples **)
(******************************************************************)

Module RobustSafety (RL : PCM_T) (C : CORE_LANG).

  Module Export Iris := IrisWP RL C.
  Local Open Scope iris_scope.
  Local Open Scope mask_scope.
  Local Open Scope pcm_scope.
  Local Open Scope bi_scope.
  Local Open Scope lang_scope.

  Implicit Types (P Q R : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (φ : value -n> Props) (r : res) (w : Wld).

  Lemma htUnsafe m P e φ : ht true m P e φ ⊑ ht false m P e φ.
  Proof.
    move=> wz nz rz He w HSw n r HLe Hr HP.
    move: {He P wz nz rz HSw HLe Hr HP} (He _ HSw _ _ HLe Hr HP).
    move: n e φ w r; elim/wf_nat_ind; move=> n IH e φ w r He.
    rewrite unfold_wp; move=> w' k rf mf σ HSw HLt HD Hw.
    move: {IH} (IH _ HLt) => IH.
    move: He => /unfold_wp He; move: {He HSw HLt HD Hw} (He _ _ _ _ _ HSw HLt HD Hw) => [HV [HS [HF _] ] ].
    split; [done | clear HV; split; [clear HF | split; [clear HS | done] ] ].
    - move=> σ' ei ei' K HK Hs.
      move: {HS HK Hs} (HS _ _ _ _ HK Hs) => [w'' [r' [HSw' [He' Hw'] ] ] ].
      exists w'' r'; split; [done | split; [exact: IH | done] ].
    move=> e' K HK.
    move: {HF HK} (HF _ _ HK) => [w'' [rfk [rret [HSw' [Hk [He' Hw'] ] ] ] ] ].
    exists w'' rfk rret; split; [done | split; [exact: IH | split; [exact: IH | done] ] ].
  Qed.

End RobustSafety.
