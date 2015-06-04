Require Import Ssreflect.ssreflect Omega.
Require Import CSetoid Predom RA DecEnsemble ModuRes.Relations.

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Set Bullet Behavior "Strict Subproofs".

(** These constructions are only for RA, so their equality is also defined locally. *)

(** The exclusive RA. *)
Section Exclusive.
  Context {T: Type} {eqT : Setoid T}.

  Inductive ex: Type :=
  | ex_own: T -> ex
  | ex_unit: ex
  | ex_bot: ex.

  Implicit Types (r s : ex) (t : T).

  Definition ex_eq r s: Prop :=
    match r, s with
      | ex_own t1, ex_own t2 => t1 == t2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Instance ra_equiv_ex : Equivalence ex_eq.
  Proof.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.

  Global Program Instance ra_type_ex : Setoid ex :=
    mkType ex_eq.

  Global Instance ex_own_compat : Proper (equiv ==> equiv) ex_own.
  Proof. by move=> t1 t2 EQt. Qed.

  Global Instance ra_unit_ex : RA_unit _ := fun _ => ex_unit.
  Global Instance ra_op_ex : RA_op _ :=
    fun r s =>
      match r, s with
        | ex_own _, ex_unit => r
        | ex_unit, ex_own _ => s
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid _ :=
    fun r => match r with
               | ex_bot => False
               | _      => True
             end.

  Global Instance ra_ex : RA ex.
  Proof.
    split.
    - intros [t1| |] [t2| |] Heqt [t'1| |] [t'2| |] Heqt'; simpl; now auto.
    - intros [s1| |] [s2| |] [s3| |]; reflexivity.
    - intros [s1| |] [s2| |]; reflexivity.
    - intros [s1| |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - intros t1 t2. exists ex_unit. reflexivity. 
    - intros [t | |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - intros [t1| |] [t2| |]; unfold ra_valid; simpl; now auto.
  Qed.

  Lemma ra_sep_ex {t r} : ↓ex_own t · r -> r == 1 r.
  Proof. by case: r. Qed.

  Lemma ra_fps_ex_any t {r} (Hr : ↓r) : ex_own t ⇝ r.
  Proof. by move=> f /ra_sep_ex ->; rewrite (ra_op_unit2 (t := r)). Qed.

  Lemma ra_fps_ex t t' : ex_own t ⇝ ex_own t'.
  Proof. exact: ra_fps_ex_any. Qed.

  Global Instance ra_can_ex : Cancellative ex.
  Proof.
    case=>[t ||] a b Hv HEq.
    - by rewrite (ra_sep_ex Hv); move: Hv; rewrite -HEq=> /ra_sep_ex->; reflexivity.
    - by move: HEq; rewrite (ra_op_unit (t:=a)) (ra_op_unit (t:=b)).
    - by exfalso.
  Qed.

  Global Instance ra_vira_ex : VIRA ex.
  Proof.
    exists ex_unit. exact I.
  Qed.

  Lemma ex_own_le t r t':
    ex_own t ⊑ r -> r ⊑ ex_own t' ->
    t == t'.
  Proof.
    move=>[r1 Heq1] [r2 Heq2]. destruct r1, r2, r; simpl in *; try contradiction; [].
    rewrite Heq1 Heq2. reflexivity.
  Qed.

End Exclusive.
Arguments ex T : clear implicits.


Section ExTests.
  Context {T : Type} {eqT : Setoid T}.
  Implicit Types (t : T).

  Goal forall t1 t2, t1 == t2 -> ex_own t1 == ex_own t2.
  Proof. move=> t1 t2 ->. reflexivity. Qed.

  Context {U} `{raU : RA U}.
  Implicit Types (u : U).
  
  Goal forall t1 t2 u, t1 == t2 -> (ex_own t1,u) ⊑ (ex_own t2,u).
  Proof. move=> t1 t2 u ->. reflexivity. Qed.

  Goal forall t u1 u2, u1 == u2 -> (ex_own t,u1) == (ex_own t,u2).
  Proof. move=> t u1 u2 ->. reflexivity. Qed.
End ExTests.

(** The authoritative RA. *)
Section Authoritative.
  Context {T} `{raT : RA T}.

  CoInductive auth := Auth of ex T * T.

  Implicit Types (x : ex T) (g t u : T) (r s : auth).

  Let auth_eq r s : Prop :=
    match r, s with
    | Auth p, Auth p' => p == p'
    end.

  Global Instance ra_equiv_auth : Equivalence auth_eq.
  Proof.
    split.
    - by move=> [p]; rewrite/auth_eq; reflexivity.
    - by move=> [p] [p']; rewrite/auth_eq; symmetry.
    - by move=> [p1] [p2] [p3]; rewrite/auth_eq; transitivity p2.
  Qed.
  Global Instance ra_type_auth : Setoid auth := mkType auth_eq.

  Section Compat.
    Variable R : relation (ex T * T).

    Let RA : relation auth := fun r1 r2 =>
      match r1, r2 with Auth p1, Auth p2 => R p1 p2 end.

    Global Instance auth_compat : Proper(R ==> RA) Auth.
    Proof. by move=> p1 p2 Rp. Qed.
  End Compat.

  Global Instance ra_unit_auth : RA_unit auth := 
    fun a => match a with 
               | Auth (e,t) => Auth(ex_unit, 1 t)
             end.

  Global Instance ra_op_auth : RA_op auth := fun r s =>
    match r, s with Auth(x, t), Auth(x', t') => Auth(x·x', t·t') end.

  Global Instance ra_valid_auth : RA_valid auth := fun r =>
    match r with
    | Auth(ex_unit, t) => ↓t
    | Auth(ex_own g, t) => ↓g /\ ↓t /\ t ⊑ g
    | Auth(ex_bot, _) => False
    end.

  Global Instance ra_auth : RA auth.
  Proof.
    split.
    - move=> [[x1 t1]] [[x1' t1']] [/= Hx1 Ht1] [[x2 t2]] [[x2' t2']] [/= Hx2 Ht2].
      by rewrite Hx1 Ht1 Hx2 Ht2; split; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] [[x3 t3]] /=; split; rewrite assoc; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] /=; split; rewrite comm; reflexivity.
    - move=> [[s t]] /=. split; last (rewrite ra_op_unit; reflexivity).
      destruct s; reflexivity.
    - move => [[x1 t1]] [[x2 t2]]. by firstorder.
    - move => [[x1 t1]] [[x2 t2]].
      destruct (ra_unit_mono x1 x2) as [x3 Hx], (ra_unit_mono t1 t2) as [t3 Ht].
      exists (Auth (x3, t3)); split; assumption. 
    - move=> [[x t]]. unfold ra_unit, ra_unit_auth. rewrite !ra_unit_idem.
      reflexivity.
    - move=> [[x t]] [[x' t']] [/= Hx Ht].
      rewrite/ra_valid/ra_valid_auth.
      move: Hx; case: x=>[g||]; case: x'=>[g'||] => //= Hg.
      + by rewrite Ht Hg.
      + by rewrite Ht.
    - move=> [[x t]] [[x' t']]. rewrite /ra_op/ra_op_auth/ra_valid/ra_valid_auth.
      case: x=>[g||]; case: x'=>[g'||] //=.
      + move=>[Hg [Htv [t'' Ht]]]; split; [done | split; [exact: ra_op_valid Htv |]].
        exists (t'' · t'); by rewrite -assoc [t' · _]comm.
      + move=>[_ [Htv _]]; exact: ra_op_valid Htv.
      + exact: ra_op_valid.
  Qed.

  Lemma ra_sep_auth {t u x u'} :
    ↓Auth(ex_own t, u) · Auth(x, u') -> ↓t /\ x == ex_unit /\ ↓u · u' /\ u · u' ⊑ t.
  Proof.
    case: x=>[g||]; [done | | done].
    rewrite {1}/ra_valid/ra_valid_auth {1}/ra_op/ra_op_auth.
    by move=> [Ht [HSep HLe]].
  Qed.

  Definition auth_side_cond t u t' (Pu': T -> Prop) : Prop :=
    ↓u -> forall tf, t · tf ⊑ u -> exists u', Pu' u' /\ t' · tf ⊑ u' /\ ↓u'.

  (* This is the strongest lemma for auth-FPU we found. Everything else will be derived from this. *)
  Lemma ra_fpu_auth_general {t u t' Pu'} {Pn': auth -> Prop} (SIDE : auth_side_cond t u t' Pu') :
    (forall u', Pu' u' -> Pn' (Auth(ex_own u', t'))) ->
    Auth(ex_own u, t) ⇝∈ Pn'.
  Proof.
    move=>HPn' [[xf tf]] /ra_sep_auth [Htu [Hxf [Htf HLe]]].
    move:(SIDE Htu _ HLe)=>{SIDE} [u' [HPu' [HLe' Hval]]].
    exists (Auth (ex_own u', t')). split; first now apply HPn'.
    rewrite/ra_valid/ra_valid_auth [Auth _ · _]/ra_op/ra_op_auth.
    move: Hxf; case: xf=>[g||] H; [done| clear H |done].	(* i.e., "rewrite Hxf" despite the match. *)
    rewrite {1}/ra_op/ra_op_ex.
    split; first done.
    split; last done.
    destruct HLe' as [w HEq].
    eapply ra_op_valid2. now erewrite HEq.
  Qed.

  (* The following two lemmas for FPU and FPS are good enough for everything we need, and they
     have a precondition that one can actually give some intuition to.
     auth_steps is slightly stronger than auth_side_cond: Think of "tf" below being
     both "tf" and the "w" hidden in ⊑ above. Then auth_side_cond allows changing
     "w" to anything else, whereas auth_steps enforces using the same "w". *)
  Definition auth_steps t u t' Pu' : Prop :=
    ↓u -> forall tf, t · tf == u -> exists u', Pu' u' /\ t' · tf == u' /\ ↓u'.
  
  Lemma ra_fpu_auth {t u t' Pu'} {Pn': auth -> Prop} (STEPS : auth_steps t u t' Pu') :
    (forall u', Pu' u' -> Pn' (Auth(ex_own u', t'))) ->
    Auth(ex_own u, t) ⇝∈ Pn'.
  Proof.
    apply ra_fpu_auth_general. move=>Hu tf [w HEq].
    specialize (STEPS Hu (tf · w)). move:STEPS. case.
    - rewrite -HEq (comm w) assoc. reflexivity.
    - move=>u' [HPu' [HEq' Hu']]. exists u'. split; first assumption. split; last assumption.
      exists w. rewrite -HEq' (comm w) assoc. reflexivity.
  Qed.

  Definition auth_step t u t' u' : Prop :=
    ↓u -> forall tf, t · tf == u -> t' · tf == u' /\ ↓u'.

  Lemma ra_fps_auth {t u t' u'} (STEP: auth_step t u t' u'):
    Auth(ex_own u, t) ⇝ Auth(ex_own u', t').
  Proof.
    apply ra_fpu_fps. eapply (ra_fpu_auth (Pu':=equiv u') (t':=t')).
    - move=>Hu tf Heq. exists u'. split; first reflexivity. exact: STEP.
    - move=>u'' ->. reflexivity.
  Qed.

  (* Some derived forms of the lemma above. But really, when proving in Coq,
     using ra_fps_auth directly is the easiest way forward *)
  Lemma ra_fps_auth_canc {HC : Cancellative T} t {u t'} (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    apply: ra_fps_auth.
    move=> Hu tf HLe.
    split; last done.
    move: Hu. move/ra_cancel. move/(_ _ HLe)=>->. reflexivity.
  Qed.

  Definition ra_local_action (act : T -=> T) : Prop :=
    forall t tf, ↓act t -> ↓t · tf -> act(t · tf) == (act t) · tf.

  Lemma ra_op_local t: ra_local_action (ra_op_s t).
  Proof.
    move=>t' tf Hact Hcomp. simpl. rewrite assoc. reflexivity.
  Qed.

  Lemma ra_fps_auth_local {act t u} (HL : ra_local_action act) (Hu' : ↓act t · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(act t · u), act t).
  Proof.
    eapply ra_fps_auth.
    move=>Hval tf HEq. split; last assumption.
    transitivity (act (t · u)).
    - rewrite -HEq. symmetry. eapply HL.
      + eapply ra_op_valid. eassumption.
      + rewrite HEq. assumption.
    - eapply HL; last assumption.
      eapply ra_op_valid. eassumption.
  Qed.
End Authoritative.
Arguments auth : clear implicits.
(*
Notation "• g" := (Auth (ex_own g,1)) (at level 48) : ra_scope.
Notation "∘ t" := (Auth (1,t)) (at level 48) : ra_scope.
*)

Section AuthTests.
  Context {T : Type} `{raT : RA T}.
  Implicit Types (x : ex T) (t : T).
  
  Goal forall x t1 t2, t1 == t2 -> Auth(x,t1) == Auth(x,t2).
  Proof. move=> x t1 t2 EQt. rewrite EQt. reflexivity. Qed.

  Goal forall x1 x2 t, x1 == x2 -> Auth(x1,t) == Auth(x2,t).
  Proof. move=> x1 x2 t EQx. rewrite EQx. reflexivity. Qed.
End AuthTests.


Section DecAgreement.
  Context T (eq_dec : DecEq T).
  Local Open Scope ra_scope.

  Inductive ra_dagree : Type :=
    | dag_bottom
    | dag_unit
    | dag_inj (t : T).

  Global Instance ra_unit_dagree : RA_unit _ := fun _ => dag_unit.
  Global Instance ra_valid_dag : RA_valid _ :=
           fun x => match x with dag_bottom => False | _ => True end.
  Global Instance ra_op_dag : RA_op _ :=
    fun x y => match x, y with
               | dag_inj t1, dag_inj t2 =>
                   if eq_dec t1 t2 is left _ then dag_inj t1 else dag_bottom
               | dag_bottom , y => dag_bottom
               | x , dag_bottom => dag_bottom
               | dag_unit, y => y
               | x, dag_unit => x
             end.

  Definition ra_eq_dag (x y: ra_dagree): Prop :=
    match x,y with
      | dag_inj t1, dag_inj t2 => t1 = t2
      | x, y => x = y
    end.


  Global Instance ra_equivalence_agree : Equivalence ra_eq_dag.
  Proof.
    split; intro; intros; destruct x; try (destruct y; try destruct z); simpl; try reflexivity;
    simpl in *; try inversion H; try inversion H0; try rewrite <- H; try rewrite <- H0; try firstorder.
  Qed.
  Global Instance ra_type_dagree : Setoid ra_dagree := mkType ra_eq_dag.
  Global Instance res_dagree : RA ra_dagree.
  Proof.
    split; repeat intro.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; try discriminate || reflexivity || assumption; [].
      unfold ra_op, ra_op_dag.
      destruct (eq_dec t2 t0), (eq_dec t1 t); simpl; auto; exfalso; apply n; congruence.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; try discriminate || reflexivity || assumption;
      compute; try destruct (eq_dec _ _); try reflexivity; [].
      destruct (eq_dec t0 t), (eq_dec t1 t0), (eq_dec t1 t); simpl; auto; exfalso; apply n; congruence.
    - destruct t1, t2; try reflexivity; compute; destruct (eq_dec t0 t), (eq_dec t t0);
      try reflexivity; auto; try contradiction; symmetry in e; contradiction.
    - destruct t; reflexivity.
    - destruct x, y; simpl; firstorder; now inversion H.
    - by exists dag_unit.
    - destruct t; reflexivity.
    - destruct x, y; simpl; firstorder; now inversion H.
    - destruct t1, t2; try contradiction; now constructor.
  Qed.

End DecAgreement.

Section STS.
  Context {S T: Type}. (* the types of states and tokens. We ignore their Setoids. *)
  Local Instance STS_States_discrete : Setoid S := discreteType.
  Definition Toks := DecEnsemble T.
  Context (step: relation S) (tok: S -> Toks).

  Local Open Scope de_scope.  

  Definition tokstep: relation (S * Toks) :=
    fun st1 st2 => match st1, st2 with
                   | (s1, t1), (s2, t2) => step s1 s2 /\ (tok s1) # t1 /\ (tok s2) # t2 /\
                                           (tok s1) ∪ t1 == (tok s2) ∪ t2
                   end.

  Local Instance tokstep_equiv: Proper (equiv ==> equiv ==> equiv) tokstep.
  Proof.
    move=>[s11 t11] [s12 t12] /= [EQs1 EQt1] [s21 t21] [s22 t22] [EQs2 EQt2]. unfold tokstep.
    simpl in *.
    hnf in EQs2. hnf in EQs1. subst.
    rewrite EQt1 EQt2. reflexivity.
  Qed.

  Definition toksteps := refl_trans_closure tokstep.

  Lemma toksteps_toks t1 s1 t2 s2:
    tok s1 # t1 ->
    toksteps (s1, t1) (s2, t2) ->
    tok s2 # t2 /\ (tok s1) ∪ t1 == (tok s2) ∪ t2.
  Proof.
    move=>Hdisj Hsteps. remember (s1, t1) as st1. remember (s2, t2) as st2.
    revert s1 t1 s2 t2 Hdisj Heqst1 Heqst2. induction Hsteps; intros; subst.
    - destruct H as [EQs EQt]. simpl in *. hnf in EQs. subst s2. rewrite EQt -EQt. now split.
    - destruct ρ2 as [s3 t3]. destruct H as [_ [Htok1 [Htok2 Hpres]]].
      move:IHHsteps. move/(_ _ _ _ _ Htok2 eq_refl). move/(_ s2 t2 eq_refl)=>[Htok3 Hpres'].
      split; first assumption.
      etransitivity; eassumption.
  Qed.

  Definition tframestep t: relation S :=
    fun s1 s2 => step s1 s2 /\ tok s1 # t /\ tok s2 # t.

  Local Instance tframestep_equiv: Proper (equiv ==> equiv ==> equiv ==> equiv) tframestep.
  Proof.
    move=>t1 t2 EQt s11 s12 EQs1 s21 s22 EQs2.
    rewrite /tframestep EQs1 EQs2 EQt. reflexivity.
  Qed.

(*  Local Instance tframestep_equiv_t t: Proper (equiv ==> equiv ==> equiv) (tframestep t).
  Proof.
    eapply tframestep_equiv. reflexivity.
  Qed.*)

  Definition tframesteps t := refl_trans_closure (tframestep t).

  Lemma tframesteps_toks t s1 s2:
    tok s1 # t ->
    tframesteps t s1 s2 ->
    tok s2 # t.
  Proof.
    move=>Htok Hstep. revert Htok. induction Hstep.
    - rewrite H. tauto.
    - destruct H as [_ Htoks]. tauto.
  Qed.

  Local Instance tframesteps_equiv: Proper (equiv ==> equiv) tframesteps.
  Proof.
    move=>t1 t2 EQt. rewrite /tframesteps.
    eapply refl_trans_closure_r_equiv.
    move=>s1 s2. now rewrite EQt.
  Qed.

  Lemma tokstep_framestep {s1 t1 s2 t2} tf:
    tf # (tok s1 ∪ t1) ->
    tokstep (s1, t1) (s2, t2) ->
    tframestep tf s1 s2.
  Proof.
    intros Hdisj (Hstep & Hdisj1 & Hdisj2 & Hpres).
    split; first assumption.
    split.
    - clear Hdisj2 Hpres. de_auto_eq.
    - clear Hdisj1. de_auto_eq.
  Qed.

  Lemma toksteps_framesteps {s1 t1 s2 t2} tf:
    tf # (tok s1 ∪ t1) ->
    toksteps (s1, t1) (s2, t2) ->
    tframesteps tf s1 s2.
  Proof.
    move=>Hdisj Hsteps. remember (s1, t1) as st1. remember (s2, t2) as st2.
    revert s1 t1 s2 t2 Hdisj Heqst1 Heqst2. induction Hsteps; intros.
    - subst. destruct H as [EQs _]. apply rt_refl. apply EQs.
    - subst. destruct ρ2 as [s3 t3]. eapply rt_step.
      + eapply tokstep_framestep; eassumption.
      + eapply IHHsteps; try reflexivity. destruct H as [_ [_ H]]. de_auto_eq.
  Qed.

  Lemma tframestep_smaller s1 s2 t1 t2:
    t1 ⊑ t2 ->
    tframestep t2 s1 s2 ->
    tframestep t1 s1 s2.
  Proof.
    intros Hle (Hstep & Hdisj1 & Hdisj2).
    split; split_conjs.
    - assumption.
    - clear Hdisj2. de_auto_eq.
    - clear Hdisj1. de_auto_eq.
  Qed.

  Lemma tframesteps_smaller s1 s2 t1 t2:
    t1 ⊑ t2 ->
    tframesteps t2 s1 s2 ->
    tframesteps t1 s1 s2.
  Proof.
    move=>Hle. induction 1.
    - now apply rt_refl.
    - eapply rt_step; last eassumption.
      eapply tframestep_smaller; eassumption.
  Qed.
    
  Definition upclosed (ss: S -> Prop) (t: Toks): Prop :=
    forall s1 s2, ss s1 -> tframesteps t s1 s2 -> ss s2.

  Lemma upclosed_bystep (ss: S -> Prop) t:
    (forall s1 s2, ss s1 -> tframestep t s1 s2 -> ss s2) ->
    upclosed ss t.
  Proof.
    move=>Hstep s1 s2 Hs1.
    induction 1.
    - rewrite -H. assumption.
    - eapply IHrefl_trans_closure, Hstep.
      + eassumption.
      + assumption.
  Qed.

  Definition upclose (ss: S -> Prop) (t: Toks): S -> Prop :=
    fun s' => exists s, ss s /\ tframesteps t s s'.

  Local Instance upclose_equiv: Proper (equiv ==> equiv ==> equiv) upclose.
  Proof.
    move=>ss1 ss2 EQss t1 t2 EQt s.
    split; intros [s' [Hs' Hstep]]; (exists s'; split; first now apply EQss).
    - eapply tframesteps_equiv; last eassumption.
      now symmetry.
    - eapply tframesteps_equiv; last eassumption.
      assumption.
  Qed.

  Lemma upclose_upclosed ss t:
    upclosed (upclose ss t) t.
  Proof.
    move=>s1 s2 [s1' [Hs1 Hsteps1]] Hsteps2.
    exists s1'. split; first assumption.
    eapply rt_trans; try (now apply _); eassumption.
  Qed.

  Lemma upclose_incl (ss: S -> Prop) t:
    forall s, ss s -> upclose ss t s.
  Proof.
    move=>s H. exists s. split; first assumption.
    apply rt_refl. reflexivity.
  Qed.

  Lemma upclose_noop (ss: S -> Prop) t (Hadisj: forall s, ss s -> tok s # t):
    upclosed ss t ->
    upclose ss t == ss.
  Proof.
    move=>Hclosed s. split.
    - move=>[s' [Hs' Hstep]].
      eapply Hclosed; eassumption.
    - eapply upclose_incl.
  Qed.

  CoInductive STSMon :=
  | STSEl: forall (ss: S -> Prop) (t: Toks) (v: Prop), upclosed ss t -> (forall s, ss s -> tok s # t) -> STSMon.

  Definition STS_ss (el: STSMon) :=
    let (ss, _, _, _, _) := el in ss.

  Definition STS_t (el: STSMon) :=
    let (_, t, _, _, _) := el in t.

  Local Ltac sts_destr := repeat (match goal with [ x : STSMon |- _ ] => destruct x end).

  Definition STS_eq: relation STSMon :=
    fun el1 el2 => match el1, el2 with
                   | STSEl ss1 t1 v1 _ _, STSEl ss2 t2 v2 _ _ => ss1 == ss2 /\ t1 == t2 /\ v1 == v2
                   end.

  Global Instance STS_equiv: Equivalence STS_eq.
  Proof.
    split.
    - intros ?. sts_destr; simpl. split_conjs; reflexivity.
    - intros ? ?. sts_destr; simpl. intros [EQs ?].
      split_conjs; now symmetry.
    - intros ? ? ?. sts_destr; simpl. intros [EQs1 [EQt1 EQv1]] [EQs2 [EQt2 EQv2]].
      split_conjs; try (etransitivity; eassumption).
  Qed.

  Global Instance STS_Type: Setoid STSMon := mkType STS_eq.

  Global Instance STS_valid: RA_valid STSMon :=
    fun el => let (ss, _, v, _, _) := el in v /\ (exists s, ss s).

  Program Definition STS_upclose (ss: S -> Prop) (t: Toks): STSMon :=
    let ss' := (fun s' => ss s' /\ tok s' # t) in
    STSEl (upclose ss' t) t True _ _.
  Next Obligation.
    apply upclose_upclosed.
  Qed.
  Next Obligation.
    destruct H as [s' [[Hss Htok]] _].
    eapply tframesteps_toks; eassumption.
  Qed.

  Definition STS_upclose1 s t := STS_upclose (fun s' => s' = s) t.
  
  Program Definition STS_upclose_notok (ss: S -> Prop): STSMon :=
    STSEl (upclose ss de_emp) de_emp True _ _.
  Next Obligation.
    apply upclose_upclosed.
  Qed.
  Next Obligation.
    rewrite de_emp_isect. reflexivity.
  Qed.

  Lemma STS_upclose_notok_eq ss:
    STS_upclose_notok ss == STS_upclose ss de_emp.
  Proof.
    split; last (split; reflexivity).
    eapply upclose_equiv; last reflexivity.
    move=>s. split; last tauto.
    move=>H. split; first eassumption.
    de_auto_eq.
  Qed.

  Definition STS_upclose1_notok (s: S): STSMon := STS_upclose_notok (fun s' => s' = s).

  Global Instance STS_unit: RA_unit STSMon :=
    fun el => let (ss, t, v, uc, d) := el in STS_upclose_notok ss.

  Global Program Instance STS_op: RA_op STSMon :=
    fun el1 el2 => match el1, el2 with
                   | STSEl ss1 t1 v1 uc1 d1, STSEl ss2 t2 v2 uc2 d2 =>
                     STSEl (fun s => ss1 s /\ ss2 s)
                           (t1 ∪ t2) (v1 /\ v2 /\ t1 # t2) _ _
                   end.
  Next Obligation.
    apply upclosed_bystep.
    move=>s1 s2 [Hss1 Hss2] Hstep.
    assert(Hss1': ss1 s2).
    { eapply uc1; first eassumption.
      eapply rt_onestep, tframestep_smaller, Hstep.
      de_auto_eq. }
    assert(Hss2': ss2 s2).
    { eapply uc2; first eassumption.
      eapply rt_onestep, tframestep_smaller, Hstep.
      de_auto_eq. }
    split_conjs; assumption.
  Qed.
  Next Obligation.
    specialize (d1 _ H). specialize (d2 _ H0). de_auto_eq.
  Qed.

  Global Instance STS_RA: RA STSMon.
  Proof.
    split.
    - intros el1 el2. sts_destr. intros [EQs1 [EQt1 EQv1]] el3 el4. sts_destr. intros [EQs3 [EQt3 EQv3]]. split; last split.
      + move=>s. simpl. rewrite (EQs1 s) (EQs3 s). reflexivity.
      + now rewrite EQt1 EQt3.
      + now rewrite EQt1 EQt3 EQv1 EQv3.
    - intros el1 el2 el3. sts_destr. split; last (split; first (now rewrite assoc)); last first.
      { split; intros H; split_conjs; try tauto; de_auto_eq. }
      intro s. split; intros [Hin1 Hin2]; tauto.
    - intros el1 el2. sts_destr. split; last (split; first (now rewrite comm)).
      + intro s. split; tauto.
      + rewrite comm. split; tauto.
    - move=>t. sts_destr. split; last (split; first now rewrite comm de_emp_union); last first.
      { split=>H; first tauto. split_conjs; try tauto; de_auto_eq. }
      move=>s. split=>Hss; first tauto.
      split_conjs.
      + exists s. split; first assumption. now apply rt_refl.
      + assumption.
    - move=>el1 el2. sts_destr. move =>[EQs [EQt EQv]]. split; last (split; reflexivity).
      rewrite EQs. reflexivity.
    - move=>t t'. exists (1 (t · t')). sts_destr. split; last (split; first now rewrite de_emp_union); last first.
      { split=>H; last tauto. split_conjs; try tauto; de_auto_eq. }
      move=>s. split.
      + intros [s' H]. split_conjs.
        * exists s'. tauto.
        * exists s'. tauto.
      + intros [_ [s'' [[Hs' Hs''] Hsteps'']]].
        exists s''. tauto.
    - move=>t. sts_destr. simpl. split; last (split; reflexivity).
      apply upclose_noop; last exact: upclose_upclosed.
      move=>s _. de_auto_eq.
    - apply proper_sym_impl_iff; try (now apply _). move=>el1 el2. sts_destr. move =>[EQs [EQt EQv]] [Hv [s Hinh]].
      split; first now apply EQv. exists s. now apply EQs.
    - move=>t1 t2. sts_destr. move=>[Hv [s Hinh]].
      split; first tauto.
      exists s. tauto.
  Qed.

  Lemma sts_pord st1 st2:
    ↓st2 ->
    (st1 ⊑ st2 <-> (↓st1 /\ STS_t st1 ⊑ STS_t st2 /\ STS_ss st2 == (fun s => STS_ss st1 s /\ upclose (STS_ss st2) (STS_t st2 \ STS_t st1) s))).
  Proof.
    move=>Hval. destruct st1 as [ss1 t1 v1 u1 d1], st2 as [ss2 t2 v2 u2 d2]. split.
    - move=>[[ss3 t3 v3 u3 d3] Heq]. split_conjs; simpl; last (destruct Heq as [Heq_ss [Heq_t Heq_v]]=>s; split).
      + eapply ra_op_valid2. erewrite Heq. assumption.
      + destruct Heq. de_auto_eq.
      + move=>Hss2. split; first now apply Heq_ss.
        exists s. split; first assumption. now apply rt_refl.
      + move=>[Hss1 [s' [Hss2 Hsteps]]]. apply Heq_ss. split; last assumption.
        eapply (u3 s'); first (now eapply Heq_ss). eapply tframesteps_smaller; last eassumption.
        destruct Hval as [Hval _]. apply Heq_v in Hval. de_auto_eq.
    - destruct Hval as [Hval Hinh]. simpl.
      move=>[[Hval' Hinh'] [Htincl Hseq]].
      exists (STS_upclose ss2 (t2 \ t1)). split; last split; last first.
      + split; first tauto. move=>_. split_conjs; try tauto. de_auto_eq.
      + de_auto_eq.
      + move=>s. split; last first.
        { move=>Hss2. split; last now apply Hseq.
          exists s. split_conjs; first assumption.
          - specialize (d2 _ Hss2). de_auto_eq.
          - apply rt_refl. reflexivity. }
        move=>[[s' [[Hss2 Htok] Hstep]] Hss1].
        apply Hseq. split; first assumption. exists s'. split; assumption.
  Qed.

  (* Now we become authoritative *)
  Definition STSauth := auth STSMon.
  Definition STSAuth := (@Auth STSMon).

  Lemma sts_fupd st_a st_l s t s' t'
    (Hstart: STS_ss st_a s /\ t = STS_t st_l) (* we start somewhere in st_a, with the tokens from st_l *) :
    toksteps (s, t) (s', t') ->
    STSAuth (ex_own st_a, st_l) ⇝∈ (fun n => exists st_an, STS_ss st_an s' /\ n == STSAuth (ex_own st_an, STS_upclose1 s' t')).
  Proof.
    destruct Hstart as [Hs Ht]. move=>Hsteps.
    eapply (ra_fpu_auth (Pu':=fun st_an => STS_ss st_an s') (t':=STS_upclose1 s' t')); last first.
    { move=>u' Hu'. exists u'. split; assumption || reflexivity. }
    move=>Hval tf HEq.
    assert (Hatoks: t ⊑ STS_t st_a).
    { sts_destr. destruct HEq as [_ [Htoks _]]. subst t. simpl. clear -Htoks. de_auto_eq. }
    assert (Hastoks: tok s # STS_t st_a).
    { clear -Hatoks Hs. destruct st_a as [? ? ? ? a_d]. simpl. eapply a_d; eassumption. }
    assert (Hsteptoks: tok s' # t' /\ tok s ∪ t == tok s' ∪ t').
    { apply toksteps_toks; last assumption. de_auto_eq. }
    assert (Htf: ↓tf).
    { eapply ra_op_valid2. erewrite HEq. assumption. }
    destruct tf as [tf_ss tf_t tf_v tf_u tf_d].
    assert (Htf_ss: tf_ss s).
    { sts_destr. destruct HEq as [Heq_ss _]. eapply Heq_ss. eexact Hs. }
    assert (Hdisj_tf: tf_t # tok s ∪ t).
    { move:(tf_d _ Htf_ss)=>Hdisj {Htf_ss}. rewrite <-HEq in Hval.
      clear -Hval Hdisj Ht. sts_destr. destruct Hval as [Hval _]. rewrite Ht /=. de_auto_eq. }
    assert (Htf_ss': tf_ss s').
    { eapply tf_u; first eexact Htf_ss.
      eapply toksteps_framesteps; eassumption. }
    exists (STS_upclose1 s' t' · (STSEl tf_ss tf_t tf_v tf_u tf_d)). split_conjs.
    - split; last assumption. exists s'. split; last now apply rt_refl.
      split; first reflexivity. tauto.
    - reflexivity.
    - split.
      + split; first done. split; first now apply Htf. de_auto_eq.
      + exists s'. split; last assumption. exists s'. split; last now apply rt_refl.
        split; first reflexivity. tauto.
  Qed.

End STS.

Section IndexedProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : forall (i : I), Type}
          {tyS : forall i, Setoid (S i)}
          {uS : forall i, RA_unit (S i)}
          {opS : forall i, RA_op (S i)}
          {vS : forall i, RA_valid (S i)}
          {raS : forall i, RA (S i)}.
  Local Open Scope ra_scope.

  Definition ra_res_infprod := forall (i : I), S i.

  Implicit Type (i : I) (f g : ra_res_infprod).

  Definition ra_eq_infprod := fun f g => forall i, f i == g i.
  Global Instance ra_equiv_infprod : Equivalence ra_eq_infprod.
  Proof. split; repeat intro; [ | rewrite (H i) | rewrite -> (H i), (H0 i) ]; reflexivity. Qed.

  Global Instance ra_type_infprod : Setoid ra_res_infprod | 15 := mkType ra_eq_infprod. (* low priority, this is a fairly generic type... *)
  Global Instance ra_unit_infprod : RA_unit ra_res_infprod := fun t => fun i => 1 (t i).
  Global Instance ra_op_infprod : RA_op ra_res_infprod := fun f g i => f i · g i.
  Global Instance ra_valid_infprod : RA_valid ra_res_infprod := fun f => forall i, ↓ (f i).
  Global Instance ra_infprod : RA ra_res_infprod.
  Proof.
    split; repeat intro.
    - exact: ra_op_proper.
    - compute; now rewrite -> (assoc (T := S i) (t1 i) (t2 i) (t3 i)).
    - compute; now rewrite -> (comm (T :=S i) (t1 i) (t2 i)).
    - compute; now rewrite -> (ra_op_unit (RA := raS i) (t := t i)).
    - compute. rewrite (H i); reflexivity.
    - exists (fun i => proj1_sig (ra_unit_mono (t i) (t' i)))=>i.
      unfold ra_op, ra_op_infprod. move:(ra_unit_mono (t i) (t' i))=>[t'' Heq].
      etransitivity; last eapply Heq. reflexivity.
    - rewrite /ra_unit /ra_unit_infprod ra_unit_idem. reflexivity.
    - compute; intros; split; intros; by move/(_ i): H0; rewrite (H i).
    - eapply (ra_op_valid (RA := raS i)); now eauto.
  Qed.
End IndexedProduct.
Arguments ra_res_infprod : default implicits.


Section HomogeneousProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : Type} `{RA S}.

  Global Instance ra_unit_homprod : RA_unit (forall (i : I), S) := ra_unit_infprod.
  Global Instance ra_op_homprod : RA_op (forall (i : I), S) := ra_op_infprod.
  Global Instance ra_valid_homprod : RA_valid (forall (i : I), S) := ra_valid_infprod.
  Global Instance ra_homprod : RA (forall (i : I), S).
  Proof.
    split; repeat intro.
    - now apply ra_op_proper.
    - now apply ra_op_assoc.
    - now apply ra_op_comm.
    - now apply ra_op_unit.
    - now apply ra_unit_proper.
    - destruct (ra_unit_mono t t') as [i Hi]. exists i. apply Hi.
    - now apply ra_unit_idem.
    - now apply ra_valid_proper.
    - eapply ra_op_valid. eapply H0.
  Qed.
End HomogeneousProduct.

