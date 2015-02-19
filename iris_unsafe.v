Set Automatic Coercions Import.
Require Import ssreflect ssrfun ssrbool eqtype.
Require Import core_lang masks iris_wp.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Module Unsafety (RL : RA_T) (C : CORE_LANG).

  Module Export Iris := IrisWP RL C.
  Local Open Scope mask_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope lang_scope.
  Local Open Scope iris_scope.

  (* PDS: Move to iris_core.v *)
  Lemma ownL_timeless {r : RL.res} :
    valid(timeless(ownL r)).
  Proof. intros w n _ w' k r' HSW HLE. auto. Qed.

  (* PDS: Hoist, somewhere. *)
  Program Definition restrictV (Q : expr -n> Props) : vPred :=
    n[(fun v => Q (` v))].
  Solve Obligations using resp_set.
  Next Obligation.
    move=> v v' Hv w k r; move: Hv.
    case: n=>[_ Hk | n]; first by exfalso; omega.
    by move=> /= ->.
  Qed.

  Implicit Types (P : Props) (i n k : nat) (safe : bool) (m : mask) (e : expr) (Q : vPred) (r : pres) (w : Wld) (σ : state).

  (* PDS: Move to iris_wp.v *)
  Lemma htUnsafe {m P e Q} : ht true m P e Q ⊑ ht false m P e Q.
  Proof.
    move=> wz nz rz He w HSw n r HLe Hr HP.
    move: {He P wz nz rz HSw HLe Hr HP} (He _ HSw _ _ HLe Hr HP).
    move: n e Q w r; elim/wf_nat_ind; move=> n IH e Q w r He.
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
  Notation "p * q" := (BI.sc p q) (at level 40, left associativity) : iris_scope. (* RJ: there's already notation for this in iris_core? *) (* PDS: The notation in Iris core uses sc : UPred (ra_pos res) -> UPred (ra_pos res) -> UPred (ra_pos res) rather than BI.sc. This variant is generic, so it survives more simplification. *)

  Lemma wpO {safe m e Q w r} : wp safe m e Q w O r.
  Proof.
    rewrite unfold_wp.
    move=> w' k rf mf σ HSw HLt HD HW.
    by exfalso; omega.
  Qed.

  (* Leibniz equality arise from SSR's case tactic.
     RJ: I could use this ;-) move to CSetoid? *) (* PDS: Feel free. I'd like to eventually get everything but the robust safety theorem out of this file. *)
  Lemma equivP {T : Type} `{eqT : Setoid T} {a b : T} : a = b -> a == b.
  Proof. by move=>->; reflexivity. Qed.

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

  Lemma wsatM {σ m} {r : res} {w n k}
      (HW : wsat σ m r w @ n) (HLe : k <= n) :
    wsat σ m r w @ k.
  Proof. by exact: (uni_pred _ _ _ _ _ HLe). Qed.

  Ltac wsatM H := solve [done | apply (wsatM H); solve [done | omega] ].

  (*
   * Robust safety:
   *
   * Assume E : Exp → Prop satisfies
   *
   *	E(fork e) = E e
   *	E(K[e]) = E e * E(K[()])
   *
   * and there exist Γ₀, Θ₀ s.t.
   *
   *	(i) for every pure reduction ς; e → ς; e',
   *		Γ₀ | □Θ₀ ⊢ E e ==>>_⊤ E e'
   *
   *	(ii) for every atomic reduction ς; e → ς'; e',
   *		Γ₀ | □Θ₀ ⊢ [E e] e [v. E v]_⊤
   *
   * Then, for every e, Γ₀ | □Θ₀ ⊢ [E e] e [v. E v]_⊤.
   *
   * The theorem has applications to security (hence the name).
   *)
  Section RobustSafety.

    (*
     * Assume primitive reductions are either pure (do not change the
     * state) or atomic (step to a value).
     *
     * PDS: I suspect we need these to prove the lifting lemmas. If
     * so, they should be in core_lang.v.
     *)

    Axiom atomic_dec : forall e, atomic e + ~atomic e.

    Axiom pure_step : forall e σ e' σ',
      ~ atomic e ->
      prim_step (e, σ) (e', σ') ->
      σ = σ'.

    Parameter E : expr -n> Props.

    (* Compatibility for those expressions wp cares about. *)
    Axiom forkE : forall e, E (fork e) == E e.
    Axiom fillE : forall K e, E (K [[e]]) == E e * E (K [[fork_ret]]).
    
    (* One can prove forkE, fillE as valid internal equalities. *)
    Remark valid_intEq {P P' : Props} (H : valid(P === P')) : P == P'.
    Proof. move=> w n r; exact: H. Qed.

    (* View shifts or atomic triples for every primitive reduction. *)
    Parameter w₀ : Wld.
    Definition valid₀ P := forall {w n r} (HSw₀ : w₀ ⊑ w), P w n r.
    
    Axiom pureE : forall {e σ e'},
      prim_step (e,σ) (e',σ) ->
      valid₀ (vs mask_full mask_full (E e) (E e')).

    Axiom atomicE : forall {e},
      atomic e ->
      valid₀ (ht false mask_full (E e) e (restrictV E)).

    Lemma robust_safety {e} : valid₀(ht false mask_full (E e) e (restrictV E)).
    Proof.
      move=> wz nz rz HSw₀ w HSw n r HLe _ He.
      have {HSw₀ HSw} HSw₀ : w₀ ⊑ w by transitivity wz.
      
      (* For e = K[fork e'] we'll have to prove wp(e', ⊤), so the IH takes a post. *)
      pose post Q := forall (v : value) w n r, (E (`v)) w n r -> (Q v) w n r.
      set Q := restrictV E; have HQ: post Q by done.
      move: {HLe} HSw₀ He HQ; move: n e w r Q; elim/wf_nat_ind;
        move=> {wz nz rz} n IH e w r Q HSw₀ He HQ.
      apply unfold_wp; move=> w' k rf mf σ HSw HLt HD HW.
      split; [| split; [| split; [| done] ] ]; first 2 last.

      (* e forks: fillE, IH (twice), forkE *)
      - move=> e' K HDec.
        have {He} He: (E e) w' k r by propsM He.
        move: He; rewrite HDec fillE; move=> [re' [rK [Hr [He' HK] ] ] ].   
        exists w' re' rK; split; first by reflexivity.
        have {IH} IH: forall Q, post Q ->
          forall e r, (E e) w' k r -> wp false mask_full e Q w' k r.
        + by move=> Q0 HQ0 e0 r0 He0; apply: (IH _ HLt); first by transitivity w.
        split; [exact: IH | split]; last first.
        + by move: HW; rewrite -Hr => HW; wsatM HW.
        have Htop: post (umconst ⊤) by done.
        by apply: (IH _ Htop e' re'); move: He'; rewrite forkE.

      (* e value: done *)
      - move=> {IH} HV; exists w' r; split; [by reflexivity | split; [| done] ].
        by apply: HQ; propsM He.
      
      (* e steps: fillE, atomic_dec *)
      move=> σ' ei ei' K HDec HStep.
      have {HSw₀} HSw₀ : w₀ ⊑ w' by transitivity w.
      move: He; rewrite HDec fillE; move=> [rei [rK [Hr [Hei HK] ] ] ].
      move: HW; rewrite -Hr => HW.
      (* bookkeeping common to both cases. *)
      have {Hei} Hei: (E ei) w' (S k) rei by propsM Hei.
      have HSw': w' ⊑ w' by reflexivity.
      have HLe: S k <= S k by omega.
      have H1ei: ra_pos_unit ⊑ rei by apply: unit_min.
      have HLt': k < S k by omega.
      move: HW; rewrite
      	{1}mask_full_union  -{1}(mask_full_union mask_emp)
      	-assoc
      => HW.
      case: (atomic_dec ei) => HA; last first.
      
      (* ei pure: pureE, IH, fillE *)
      - move: (pure_step _ _ _ _ HA HStep) => {HA} Hσ.
        rewrite Hσ in HStep HW => {Hσ}.
        move: (pureE HStep) => {HStep} He.
        move: {He} (He w' (S k) r HSw₀) => He.
        move: {He HLe H1ei Hei} (He _ HSw' _ _ HLe H1ei Hei) => He.
        move: {HD} (mask_emp_disjoint (mask_full ∪ mask_full)) => HD.
        move: {He HSw' HW} (He _ _ _ _ _ HSw' HLt' HD HW) => [w'' [r' [HSw' [Hei' HW] ] ] ].
        move: HW; rewrite assoc=>HW.
        pose↓ α := (ra_proj r' · ra_proj rK).
        + by apply wsat_valid in HW; auto_valid.
        have {HSw₀} HSw₀: w₀ ⊑ w'' by transitivity w'.
        exists w'' α; split; [done| split]; last first.
        + by move: HW; rewrite 2! mask_full_union => HW; wsatM HW.
        apply: (IH _ HLt _ _ _ _ HSw₀); last done.
        rewrite fillE; exists r' rK; split; [exact: equivP | split; [by propsM Hei' |] ].
        have {HSw} HSw: w ⊑ w'' by transitivity w'.
        by propsM HK.

      (* ei atomic: atomicE, IH, fillE *)
      move: (atomic_step _ _ _ _ HA HStep) => HV.
      move: (atomicE HA) => He {HA}.
      move: {He} (He w' (S k) rei HSw₀) => He.
      move: {He HLe H1ei Hei} (He _ HSw' _ _ HLe H1ei Hei) => He.
      (* unroll wp(ei,E)—step case—to get wp(ei',E) *)
      move: He; rewrite {1}unfold_wp => He.
      move: {HD} (mask_emp_disjoint mask_full) => HD.
      move: {He HSw' HLt' HW} (He _ _ _ _ _ HSw' HLt' HD HW) => [_ [HS _] ].
      have Hεei: ei = ε[[ei]] by rewrite fill_empty.
      move: {HS Hεei HStep} (HS _ _ _ _ Hεei HStep) => [w'' [r' [HSw' [He' HW] ] ] ].
      (* unroll wp(ei',E)—value case—to get E ei' *)
      move: He'; rewrite {1}unfold_wp => He'.
      move: HW; case Hk': k => [| k'] HW.
      - by exists w'' r'; split; [done | split; [exact: wpO | done] ].
      have HSw'': w'' ⊑ w'' by reflexivity.
      have HLt': k' < k by omega.
      move: {He' HSw'' HLt' HD HW} (He' _ _ _ _ _ HSw'' HLt' HD HW) => [Hv _].
      move: HV; rewrite -(fill_empty ei') => HV.
      move: {Hv} (Hv HV) => [w''' [rei' [HSw'' [Hei' HW] ] ] ].
      (* now IH *)
      move: HW; rewrite assoc => HW.
      pose↓ α := (ra_proj rei' · ra_proj rK).
      + by apply wsat_valid in HW; auto_valid.
      exists w''' α. split; first by transitivity w''.
      split; last by rewrite mask_full_union -(mask_full_union mask_emp).
      rewrite/= in Hei'; rewrite fill_empty -Hk' in Hei' * => {Hk'}.
      have {HSw₀} HSw₀ : w₀ ⊑ w''' by transitivity w''; first by transitivity w'.
      apply: (IH _ HLt _ _ _ _ HSw₀); last done.
      rewrite fillE; exists rei' rK; split; [exact: equivP | split; [done |] ].
      have {HSw HSw' HSw''} HSw: w ⊑ w''' by transitivity w''; first by transitivity w'.
      by propsM HK.
    Qed.
    
  End RobustSafety.
  
End Unsafety.
