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

  (* PDS: Why isn't this inferred automatically? If necessary, move this to ris_core.v *)
  Global Program Instance res_preorder : PreOrder (pcm_ord res) := @preoPO res (PCM_preo res).

  (* PDS: Move to iris_core.v *)
  Lemma ownL_timeless {r : option RL.res} :
    valid(timeless(ownL r)).
  Proof. intros w n _ w' k r' HSW HLE; now destruct r. Qed.

  (* PDS: Hoist, somewhere. *)
  Program Definition restrictV (Q : expr -n> Props) : vPred :=
    n[(fun v => Q (` v))].
  Solve Obligations using resp_set.
  Next Obligation.
    move=> v v' Hv w k r; move: Hv.
    case: n=>[_ Hk | n].
    - by absurd (k < 0); omega.
    by move=> /= ->.
  Qed.

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
     * adv e: own ghost prim_of e.
     *)

    Program Definition adv : expr -n> Props :=
      n[(fun e => ownL(Some(prim_of e)))].
    Next Obligation. (* Poper (dist n ==> dist n) (fun e => ownRL (prim_of e)) *)
      move=> e e' HEq w k r HLt /=.
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
        apply: (IH _ HLt _ _); rewrite/=/pcm_ord; exists r'.
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
      + by move=> e0 r0 He0; apply: (IH _ HLt).
      split; [| split ].
      + by apply IH; rewrite/=; exists r'; rewrite pcm_op_comm Hrret.
      + by apply IH; reflexivity.
      by rewrite He; wsatM HW.
    Qed.

    (*
     * Boring facts about adv.
     *)

    Lemma adv_timeless {e} :
      valid(timeless(adv e)).
    Proof. exact: ownL_timeless. Qed.

    Lemma adv_dup {e} :
      valid(adv e → adv e * adv e).
    Proof.
      move=> _ _ _ w' _ k r' _ _ [β Hβ].
      have Hdup: Some(ɑ e) == Some(ɑ e)· Some(ɑ e).
      - rewrite/pcm_op/res_op/pcm_op_prod pcm_op_unit.
        by move/prim_res_eq_hack: (prim_dup e) => <-.
      move: Hβ; rewrite Hdup pcm_op_assoc.
      case Hβe: (Some _ · _) => [βe |]; last done.
      case Hβee: (_ · _) => [βee |] Hβ; last done.
      exists βe (ɑ e); split; [| split].
      - by move: Hβee Hβ; rewrite /= => -> ->.
      - by rewrite/=; exists β; move: Hβe; rewrite /= => ->.
      by rewrite/=; reflexivity.
    Qed.

    Lemma adv_fork {e} :
      valid(adv (fork e) ↔ adv e).
    Proof. by move=> w n r /=; rewrite prim_of_fork; tauto. Qed.

    Lemma adv_fork_ret :
      valid(adv fork_ret).
    Proof.
      move=> w n r /=; rewrite prim_of_fork_ret /=.
      by exists r; rewrite pcm_op_comm pcm_op_unit.
    Qed.

    Lemma adv_split {K e} :
      valid(adv (K [[e]]) ↔ adv e * adv (K [[fork_ret]])).
    Proof.
      move=> w n r /=; split; move=> {w n r} _ _ _ r _ _.
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

    (*
     * More assumptions about primitive reduction.
     *
     * I suspect we need these to prove the lifting lemmas. If so,
     * they should be in core_lang.v.
     *)
    Hypothesis atomic_dec : forall e, atomic e + ~atomic e.
    
    Hypothesis pure_step : forall e σ e' σ',
      ~ atomic e ->
      prim_step (e, σ) (e', σ') ->
      σ = σ'.

    (*
     * Proof of concept: Improving the user-interface.
     *
     * We can implement adv_step assuming
     *
     * • view shifts adv(e) ==>>_⊤ adv(e') for each pure reduction e →
     * e' and
     *
     * • triples {adv(e)} e {v. adv(v)} for each atomic reduction ς; e
     * → ς'; e'.
     *
     * These view shifts and atomic reductions need only be valid
     * after some w₀ with user-supplied invariants.
     *)

    Variable w₀ : Wld.
    
    Definition valid₀ P := forall {w n r} (HSw₀ : w₀ ⊑ w), P w n r.

    Hypothesis adv_step_pure : forall {e σ e'}
        (HStep : prim_step (e,σ) (e',σ)),
      valid₀ (vs mask_full mask_full (adv e) (adv e')).
    
    Hypothesis adv_step_atomic : forall {e σ e' σ'}
        (HStep : prim_step (e,σ) (e',σ'))
        (HV : is_value e'),
      valid₀ (ht false mask_full (adv e) e (restrictV adv)).
    
    (* This is not precisely what we assumed earlier. The extra factor
    * r' shouldn't matter once we merge the proofs.
     *)
    Lemma adv_step₀ {e σ e' σ' rf w k}
        (HSw₀ : w₀ ⊑ w)
        (HStep : prim_step (e,σ) (e',σ'))
        (HW : wsat σ mask_full (Some (ɑ e) · rf) w @ S k) :
      exists w' (r' : option res), w ⊑ w' /\
        wsat σ' mask_full (Some (ɑ e') · r' · rf) w' @ k.
    Proof.
      (* common setup. *)
      case Hα: (Some (ɑ e) · rf) => [α |]; last first.
      - by exfalso; rewrite Hα in HW; exact: (wsat_nz HW).
      have HSw : w ⊑ w by reflexivity.
      have HLe : S k <= S k by omega.
      have H1e : pcm_unit res ⊑%pcm ɑ e by exact: unit_min.
      have Hee : ɑ e ⊑%pcm ɑ e by reflexivity.
      have HLt : k < S k by omega.
      move: (mask_full_union mask_emp) => Hrew.
      move: HW; rewrite -{1}Hrew => HW {Hrew}.
      case: (atomic_dec e) => HA.
      - (* atomic reduction *)
        move: (atomic_step _ _ _ _ HA HStep) => HV {HA}.
        move: (adv_step_atomic _ _ _ _ HStep HV) => He.
        move: {He Hα HSw₀} (He w (S k) α HSw₀) => He.
        move: {He HLe H1e Hee α} (He _ HSw _ _ HLe H1e Hee) => He.
        move: He; rewrite unfold_wp => He.
        move: (mask_emp_disjoint mask_full) => HD.
        move: {He HSw HLt HW} (He _ _ _ _ _ HSw HLt HD HW) => [_ [HS _] ].
        have Hεe: e = ε[[e]] by move: (fill_empty e)->.
        move: {HS Hεe HStep} (HS _ _ _ _ Hεe HStep) => [w' [r [HSw' [He' HW] ] ] ].
        (* unroll wp a second time. *)
        move: He'; rewrite unfold_wp => He'.
        case Hk': k => [| k']; first by exists w' rf; split.	(* vacuous *)
        have HSw: w' ⊑ w' by reflexivity.
        have HLt: k' < k by omega.
        move: HW; rewrite Hk' => HW.
        move: {He' HSw HLt HD HW} (He' _ _ _ _ _ HSw HLt HD HW) => [Hv _].
        move: HV; rewrite -(fill_empty e') => HV.
        move: {Hv} (Hv HV) => [w'' [r' [HSw'' [ [α Hα] HW] ] ] ].
        move: Hα.
        have ->: (Some (ɑ ` (exist is_value (ε [[e']]) HV))) = Some (ɑ ε [[e']]) by done.
        rewrite pcm_op_comm.
        case Hαe: (_ · _) => [αe |] => Hα; last done.
        move: HW; rewrite -Hα -Hαe mask_full_union => HW.
        by exists w'' (Some α); split; first by transitivity w'.
      (* pure reduction *)
      move: (pure_step _ _ _ _ HA HStep) => {HA} Hσ.
      rewrite Hσ in HStep HW => {Hσ}.
      move: (adv_step_pure _ _ _ HStep) => {HStep} He.
      move: {He Hα HSw₀} (He w (S k) α HSw₀) => He.
      move: {He HLe H1e Hee α} (He _ HSw _ _ HLe H1e Hee) => He.
      move: (mask_emp_disjoint (mask_full ∪ mask_full)) => HD.
      move: {He HSw HLt HW} (He _ _ _ _ _ HSw HLt HD HW) => [w' [r' [HSw [ [α Hα] HW] ] ] ].
      move: HW; rewrite mask_full_union	(* r' · rf *)
      	-Hα	(* (α · e') · rf) *)
      	-[Some α · _]pcm_op_comm	(* (e' · α) · rf *)
      => HW {Hα}.
      by exists w' (Some α); split; [done | by wsatM HW].
    Qed.
        
  End RobustSafety.

End Unsafety.
