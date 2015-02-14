Set Automatic Coercions Import.
Require Import ssreflect ssrfun ssrbool eqtype seq fintype.
Require Import core_lang masks iris_wp.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Delimit Scope mask_scope with mask.

Module Unsafety (RL : PCM_T) (C : CORE_LANG).

  Module Export Iris := IrisWP RL C.
  Local Open Scope mask_scope.	(* clobbers == *)
  Local Open Scope pcm_scope.
  Local Open Scope type_scope.	(* so == means setoid equality *)
  Local Open Scope bi_scope.
  Local Open Scope lang_scope.
  Local Open Scope iris_scope.

  Implicit Types (P Q R : Props) (i n k : nat) (safe : bool) (m : mask) (e : expr) (φ : value -n> Props) (r : res) (w : Wld).

  (* PDS: Move to iris_wp.v *)
  Lemma htUnsafe {m P e φ} : ht true m P e φ ⊑ ht false m P e φ.
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

  (*
	Adjustments.

	PDS: Should be moved or discarded.
  *)
  Definition iffBI {T : Type} `{_ : ComplBI T} (p q : T) :=
    (BI.and (BI.impl p q) (BI.impl q p)).

  Notation "P ↔ Q" := (iffBI P Q) (at level 95, no associativity) : iris_scope.
  Notation "p * q" := (BI.sc p q) (at level 40, left associativity) : iris_scope.

  Notation "a ⊑%pcm b" := (pcm_ord _ a b) (at level 70, no associativity) : pcm_scope.

  Lemma wpO {safe m e φ w r} : wp safe m e φ w O r.
  Proof.
    rewrite unfold_wp.
    move=> w' k rf mf σ HSw HLt HD HW.
    by absurd (k < 0); omega.
  Qed.

  (* Easier to apply (with SSR, at least) than wsat_not_empty. *)
  Lemma wsat_nz {σ m w k} : ~ wsat σ m 0 w (S k) tt.
  Proof. by move=> [rs [HD _] ]; exact: HD. Qed.

  (*
	Simple monotonicity tactics for props and wsat.

	The tactic propsM H proves P w' n' r' given H : P w n r when
		w ⊑ w', n' <= n, r ⊑ r'
	are immediate.

	The tactic wsatM is similar.

	PDS: Should be moved.
  *)

  Lemma propsM {P w n r w' n' r'}
      (HP : P w n r) (HSw : w ⊑ w') (HLe : n' <= n) (HSr : r ⊑ r') :
    P w' n' r'.
  Proof. by apply: (mu_mono _ _ P _ _ HSw); exact: (uni_pred _ _ _ _ _ HLe HSr). Qed.

  Ltac propsM H := solve [ done | apply (propsM H); solve [ done | reflexivity | omega ] ].

  Lemma wsatM {σ m} {r : option res} {w n k}
      (HW : wsat σ m r w @ n) (HLe : k <= n) :
    wsat σ m r w @ k.
  Proof. by exact: (uni_pred _ _ _ _ _ HLe). Qed.

  Ltac wsatM H := solve [done | apply (wsatM H); solve [done | omega] ].

  Notation "'ℊ' a" := (pcm_unit(pcm_res_ex state), a)
    (at level 41, format "ℊ  a") : iris_scope.

  Section RobustSafety.

    (* The adversarial resources in e. *)
    Variable prim_of : expr -> RL.res.
    
    Variable prim_dup : forall {e},	(* Irrelevant to robust_safety. *)
      Some(prim_of e) == Some(prim_of e) · Some(prim_of e).

    (* Compatibility. *)
  
    Hypothesis prim_of_fork : forall {e},
      prim_of (fork e) == prim_of e.
  
    Hypothesis prim_of_fork_ret :	(* Irrelevant to robust_safety. *)
      prim_of fork_ret == pcm_unit RL.res.
  
    Hypothesis prim_of_split : forall {K e},
      Some(prim_of (K [[e]])) == Some(prim_of e) · Some(prim_of (K [[fork_ret]])).
  
    (*
     * Adversarial steps need only adversarial resources and preserve
     * any frame and all invariants.
     *)

    Notation "'ɑ' e" := (ℊ (prim_of e))
      (at level 41, format "ɑ  e") : iris_scope.	(* K[[e]] at level 40 *)
  
    Hypothesis adv_step : forall {e σ e' σ' rf w k},
      prim_step (e,σ) (e',σ') ->
      wsat σ mask_full (Some (ɑ e) · rf) w @ S k ->
      exists w', w ⊑ w' /\
        wsat σ' mask_full (Some (ɑ e') · rf) w' @ k.

    (*
     * Lift compatibility to full resources. (Trivial.)
     *)

    Lemma res_of_fork {e} :
      ɑ fork e == ɑ e.
    Proof. by rewrite prim_of_fork. Qed.

    Lemma res_of_fork_ret :	(* Irrelevant to robust_safety. *)
      ɑ fork_ret == ℊ pcm_unit(RL.res).
    Proof. by rewrite prim_of_fork_ret. Qed.

    (* PDS: Is there a cleaner way? *)
    Lemma prim_res_eq_hack {a b : option RL.res} : a == b -> a = b.
    Proof.
      rewrite/=/opt_eq.
      by case Ha: a=>[a' |]; case Hb: b=>[b' |]; first by move=>->.
    Qed.

    Lemma res_of_split {K e} :
      Some (ɑ K [[e]]) == Some(ɑ e) · Some(ɑ K [[fork_ret]]).
    Proof.
      rewrite /pcm_op/res_op/pcm_op_prod.
      case Hp: (_ · _)=>[p |]; last done.
      rewrite /pcm_op/= in Hp; case: Hp=><-.
(*
      rewrite -prim_of_split.

Maybe I'm missing some instances (rewrite, erewrite also fail):
	Error:
	Tactic failure:Unable to satisfy the rewriting constraints.
	Unable to satisfy the following constraints:
	EVARS:
	 ?8556==[K e p _pattern_value_ _rewrite_rule_
	          (do_subrelation:=do_subrelation)
	          |- Proper (eq ==> flip impl) (SetoidClass.equiv (Some (ɑ K [[e]])))]
	          (internal placeholder)
	 ?8555==[K e p _pattern_value_ _rewrite_rule_
	          |- subrelation SetoidClass.equiv eq] (internal placeholder)
But I can hack around it...
*)
      move: (@prim_of_split K e) => /prim_res_eq_hack Hsplit.
      by rewrite -Hsplit.
    Qed.

    (*
     * The predicate adv e internalizes ɑ e ⊑ -.
     *)

    Definition advP e r := ɑ e ⊑ r.

    Program Definition adv : expr -n> Props :=
      n[(fun e => m[(fun w => mkUPred (fun n r => advP e r) _)])].
    Next Obligation.
      move=> n k r r' HLe [α Hr'] [β Hr]; rewrite/advP.
      move: Hr'; move: Hr<-;
      rewrite	(* α · (β · e) *)
      	[Some β · _]pcm_op_comm	(* α · (e · β) *)
      	pcm_op_assoc	(* (α · e) · β *)
      	[Some α · _]pcm_op_comm	(* (e · α) · β *)
      	-pcm_op_assoc	(* e · (α · β) *)
      	pcm_op_comm	(* (α · β) · e *)
      => Hr'.
      move: Hr'; case Hαβ: (Some α · _) => [αβ |] Hr'; last done.
      by exists αβ.
    Qed.
    Next Obligation. done. Qed.
    Next Obligation. by move=> w w' HSw. Qed.
    Next Obligation. (* use the def of discrete e = n = e' *)
      move=> e e' HEq w k r HLt; rewrite/=/advP.
      move: HEq HLt; case: n=>[| n'] /= HEq HLt.
      - by absurd(k < 0); omega.
      by rewrite HEq.
    Qed.

    Lemma robust_safety {e} : valid (ht false mask_full (adv e) e (umconst ⊤)).
    Proof.
      move=> wz nz rz w HSw n r HLe _ He.
      move: {HSw HLe} He; move: n e w r; elim/wf_nat_ind; move=> {wz nz rz} n IH e w r He.
      rewrite unfold_wp; move=> w' k rf mf σ _ HLt _ HW.
      split; [| split; [| split; [| done] ] ].

      (* e value *)
      - by move=> {IH HLt} HV; exists w' r; split; [by reflexivity | done].

      (* e steps *)
      - move=> σ' ei ei' K HDec HStep.
        move: He; move: HDec->; move=> [r' He].
        move: He;	(* r' · K[ei] *)
        rewrite
        	pcm_op_comm	(* K[ei] · r' *)
        	res_of_split	(* (ei · K) · r' *)
        	-pcm_op_assoc	(* ei · (K · r') *)
        => He.
        move: HW; rewrite {1}mask_full_union => HW.
(* Bug?: Error: tampering with discharged assumptions of "in" tactical
        rewrite mask_full_union in HW.
*)
        move: HW; rewrite -He -pcm_op_assoc; move=> {He} HW.
        move: {HStep HW} (adv_step _ _ _ _ _ _ _ HStep HW) => [w'' [HSW' HW'] ].
        move: HW';	(* ei' · ((K · r') · rf) *)
        rewrite
        	pcm_op_assoc	(* ei' · (K · (r' · rf)) *)
        	pcm_op_assoc	(* ((ei' · K) · r') · rf *)
        	-res_of_split	(* (K[ei]' · r') · rf *)
        => HW'.
        move: HW' HLt; case HEq: k=>[| k'] HW' HLt.
        + by exists w' r'; split; [by reflexivity | split; [exact: wpO| done] ].
        move: HW'; case Hr': (Some _ · Some _) => [r'' |] HW'; last first.
        + by rewrite pcm_op_zero in HW'; exfalso; exact: (wsat_nz HW').
        exists w'' r''; split; [done | split; [| by rewrite mask_full_union] ].
        apply: (IH _ HLt _ _); rewrite/=/advP/=/pcm_ord; exists r'.
        by rewrite pcm_op_comm -Hr'; reflexivity.

      (* e forks *)
      move=> e' K HDec.
      move: He; move: HDec->; move=> [r' He].
      move: He;	(* r' · K[fork e'] *)
      rewrite
      	res_of_split	(* r' · (fork e' · K) *)
      	res_of_fork	(* r' · (e' · K) *)
      	pcm_op_comm	(* (e' · K) · r' *)
      	-pcm_op_assoc.	(* e' · (K · r') *)
      case Hrret: (_ · Some r') => [rret |] He; last done.
      exists w' (ɑ e') rret; split; first by reflexivity.
      have {IH} IH: forall e r, ɑ e ⊑ r -> (wp false mask_full e (umconst top)) w' k r.
      + by move=> e0 r0 He0; apply: (IH _ HLt); rewrite/=/advP.
      split; [| split ].
      + by apply IH; rewrite/=; exists r'; rewrite pcm_op_comm Hrret.
      + by apply IH; reflexivity.
      by rewrite He; wsatM HW.
    Qed.

    (*
     * Facts about adv.
     *)

    Lemma adv_timeless {e} :
      valid(timeless(adv e)).
    Proof. by move=> w n _ w' k r HSW HLe; rewrite/=/advP. Qed.

    Lemma adv_dup {e} :
      valid(adv e → adv e * adv e).
    Proof.
      move=> _ _ _ w' _ k r' _ _ [β Hβ]; rewrite/=/advP.
      have Hdup: Some(ɑ e) == Some(ɑ e)· Some(ɑ e).
      - rewrite/pcm_op/res_op/pcm_op_prod pcm_op_unit.
        by move/prim_res_eq_hack: (prim_dup e) => <-.
      move: Hβ; rewrite Hdup pcm_op_assoc.
      case Hβe: (Some _ · _) => [βe |]; last done.
      case Hβee: (_ · _) => [βee |] Hβ; last done.
      exists βe (ɑ e); split; [| split].
      - by move: Hβee Hβ; rewrite /= => -> ->.
      - by rewrite/=; exists β; move: Hβe; rewrite /= => ->.
      by reflexivity.
    Qed.

    Lemma adv_fork {e} :
      valid(adv (fork e) ↔ adv e).
    Proof. by move=> w n r; rewrite/=/advP prim_of_fork; tauto. Qed.

    Lemma adv_fork_ret :
      valid(adv fork_ret).
    Proof.
      move=> w n r; rewrite/=/advP prim_of_fork_ret /=.
      by exists r; rewrite pcm_op_comm pcm_op_unit.
    Qed.

    Lemma adv_split {K e} :
      valid(adv (K [[e]]) ↔ adv e * adv (K [[fork_ret]])).
    Proof.
      move=> w n r; rewrite/=/advP; split; move=> {w n r} _ _ _ r _ _.
      - move=> [β].
        rewrite	(* β · K[e] *)
        	res_of_split	(* β · (e · K) *)
        	pcm_op_assoc.	(* (β · e) · K) *)
        case Hβe: (Some β · _)=>[βe |] Hβ; last done.
        exists βe (ɑ K[[fork_ret]]); split; [done | split; [| by reflexivity] ].
        + by exists β; rewrite Hβe.
      move=> [α [β [Hαβ [ [α' Hα'e] [β' Hβ'K] ] ] ] ].
      move: Hαβ; move: Hβ'K <-; move: Hα'e <-.
      rewrite	(* (α' · e) · (β' · K) *)
      	[Some β' · _]pcm_op_comm	(* (α' · e) · (K · β') *)
      	pcm_op_assoc	(* ((α' · e) · K) · β') *)
      	-[_ · Some(ɑ K [[fork_ret]]) ]pcm_op_assoc	(* (α' · (e · K)) · β' *)
      	-res_of_split	(* (α' · K[e]) · β' *)
      	[Some α' · _]pcm_op_comm	(* (K[e] · α) · β' *)
      	-pcm_op_assoc	(* K[e] · (α' · β') *)
      	pcm_op_comm.	(* (α' · β') · K[e] *)
      case Hαβ: (Some α' · _) => [αβ |]; last done.
      by exists αβ.
    Qed.

  End RobustSafety.

End Unsafety.
