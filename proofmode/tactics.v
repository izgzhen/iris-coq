From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.algebra Require Export upred.
From iris.proofmode Require Export classes notation.
From iris.proofmode Require Import class_instances.
From iris.prelude Require Import stringmap hlist.

Declare Reduction env_cbv := cbv [
  env_lookup env_fold env_lookup_delete env_delete env_app env_replace
  decide (* operational classes *)
  sumbool_rec sumbool_rect (* sumbool *)
  bool_eq_dec bool_rec bool_rect bool_dec eqb andb (* bool *)
  assci_eq_dec ascii_to_digits Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  string_eq_dec string_rec string_rect (* strings *)
  env_persistent env_spatial env_spatial_is_nil
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
    envs_simple_replace envs_replace envs_split envs_clear_spatial
    envs_split_go envs_split].
Ltac env_cbv :=
  match goal with |- ?u => let v := eval env_cbv in u in change v end.

(** * Misc *)
(* Tactic Notation tactics cannot return terms *)
Ltac iFresh' H :=
  lazymatch goal with
  |- of_envs ?Δ ⊢ _ =>
     (* [vm_compute fails] if any of the hypotheses in [Δ] contain evars, so
     first use [cbv] to compute the domain of [Δ] *)
     let Hs := eval cbv in (envs_dom Δ) in
     eval vm_compute in (fresh_string_of_set H (of_list Hs))
  | _ => H
  end.
Ltac iFresh := iFresh' "~".

Tactic Notation "iTypeOf" constr(H) tactic(tac):=
  let Δ := match goal with |- of_envs ?Δ ⊢ _ => Δ end in
  match eval env_cbv in (envs_lookup H Δ) with
  | Some (?p,?P) => tac p P
  end.

Ltac iMatchGoal tac :=
  match goal with
  | |- context[ environments.Esnoc _ ?x ?P ] => tac x P
  end.

(** * Start a proof *)
Tactic Notation "iProof" :=
  lazymatch goal with
  | |- of_envs _ ⊢ _ => fail "iProof: already in Iris proofmode"
  | |- True ⊢ _ => apply tac_adequate
  | |- _ ⊢ _ => apply uPred.wand_entails, tac_adequate
  end.

(** * Context manipulation *)
Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
  eapply tac_rename with _ H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [env_cbv; reflexivity || fail "iRename:" H1 "not found"
    |env_cbv; reflexivity || fail "iRename:" H2 "not fresh"|].

Tactic Notation "iClear" constr(Hs) :=
  let rec go Hs :=
    match Hs with
    | [] => idtac
    | "★" :: ?Hs => eapply tac_clear_spatial; [env_cbv; reflexivity|go Hs]
    | ?H :: ?Hs =>
       eapply tac_clear with _ H _ _; (* (i:=H) *)
         [env_cbv; reflexivity || fail "iClear:" H "not found"|go Hs]
    end in
  let Hs := words Hs in go Hs.

(** * Assumptions *)
Tactic Notation "iExact" constr(H) :=
  eapply tac_assumption with H _ _; (* (i:=H) *)
    [env_cbv; reflexivity || fail "iExact:" H "not found"
    |let P := match goal with |- FromAssumption _ ?P _ => P end in
     apply _ || fail "iExact:" H ":" P "does not match goal"].

Tactic Notation "iAssumptionCore" :=
  let rec find Γ i P :=
    match Γ with
    | Esnoc ?Γ ?j ?Q => first [unify P Q; unify i j| find Γ i P]
    end in
  match goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs) = Some (_, ?P) =>
     first [is_evar i; fail 1 | env_cbv; reflexivity]
  | |- envs_lookup ?i (Envs ?Γp ?Γs) = Some (_, ?P) =>
     is_evar i; first [find Γp i P | find Γs i P]; env_cbv; reflexivity
  end.

Tactic Notation "iAssumption" :=
  let Hass := fresh in
  let rec find p Γ Q :=
    match Γ with
    | Esnoc ?Γ ?j ?P => first
       [pose proof (_ : FromAssumption p P Q) as Hass;
        apply (tac_assumption _ j p P); [env_cbv; reflexivity|apply Hass]
       |find p Γ Q]
    end in
  match goal with
  | |- of_envs (Envs ?Γp ?Γs) ⊢ ?Q =>
     first [find true Γp Q | find false Γs Q
           |fail "iAssumption:" Q "not found"]
  end.

(** * False *)
Tactic Notation "iExFalso" := apply tac_ex_falso.

(** * Making hypotheses persistent or pure *)
Local Tactic Notation "iPersistent" constr(H) :=
  eapply tac_persistent with _ H _ _ _; (* (i:=H) *)
    [env_cbv; reflexivity || fail "iPersistent:" H "not found"
    |let Q := match goal with |- IntoPersistentP ?Q _ => Q end in
     apply _ || fail "iPersistent:" Q "not persistent"
    |env_cbv; reflexivity|].

Local Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with _ H _ _ _; (* (i:=H1) *)
    [env_cbv; reflexivity || fail "iPure:" H "not found"
    |let P := match goal with |- IntoPure ?P _ => P end in
     apply _ || fail "iPure:" P "not pure"
    |intros pat].

Tactic Notation "iPureIntro" :=
  eapply tac_pure_intro;
    [let P := match goal with |- FromPure ?P _ => P end in
     apply _ || fail "iPureIntro:" P "not pure"|].

(** Framing *)
Local Ltac iFrameFinish :=
  lazy iota beta;
  try match goal with
  | |- _ ⊢ True => exact (uPred.pure_intro _ _ I)
  end.

Local Ltac iFramePure t :=
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [apply _ || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Local Ltac iFrameHyp H :=
  eapply tac_frame with _ H _ _ _;
    [env_cbv; reflexivity || fail "iFrame:" H "not found"
    |let R := match goal with |- Frame ?R _ _ => R end in
     apply _ || fail "iFrame: cannot frame" R
    |iFrameFinish].

Local Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Local Ltac iFrameAnyPersistent :=
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := eval cbv in (env_dom (env_persistent Δ)) in go Hs
  end.

Local Ltac iFrameAnySpatial :=
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
  end.

Tactic Notation "iFrame" := iFrameAnySpatial.

Tactic Notation "iFrame" "(" constr(t1) ")" :=
  iFramePure t1.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" :=
  iFramePure t1; iFrame ( t2 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" :=
  iFramePure t1; iFrame ( t2 t3 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ).

Tactic Notation "iFrame" constr(Hs) :=
  let rec go Hs :=
    match Hs with
    | [] => idtac
    | "%" :: ?Hs => iFrameAnyPure; go Hs
    | "#" :: ?Hs => iFrameAnyPersistent; go Hs
    | "★" :: ?Hs => iFrameAnySpatial; go Hs
    | ?H :: ?Hs => iFrameHyp H; go Hs
    end
  in let Hs := words Hs in go Hs.
Tactic Notation "iFrame" "(" constr(t1) ")" constr(Hs) :=
  iFramePure t1; iFrame Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")"
    constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ) Hs.

(** * Specialize *)
Record iTrm {X As} :=
  ITrm { itrm : X ; itrm_vars : hlist As ; itrm_hyps : string }.
Arguments ITrm {_ _} _ _ _.

Notation "( H $! x1 .. xn )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) "") (at level 0, x1, xn at level 9).
Notation "( H $! x1 .. xn 'with' pat )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) pat) (at level 0, x1, xn at level 9).
Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).

Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  match xs with
  | hnil => idtac
  | _ =>
    eapply tac_forall_specialize with _ H _ _ _ xs; (* (i:=H) (a:=x) *)
      [env_cbv; reflexivity || fail 1 "iSpecialize:" H "not found"
      |let P := match goal with |- ForallSpecialize _ ?P _ => P end in
       apply _ || fail 1 "iSpecialize:" P "not a forall of the right arity or type"
      |cbn [himpl hcurry]; reflexivity|]
  end.

Local Tactic Notation "iSpecializePat" constr(H) constr(pat) :=
  let solve_to_wand H1 :=
    let P := match goal with |- IntoWand ?P _ _ => P end in
    apply _ || fail "iSpecialize:" P "not an implication/wand" in
  let rec go H1 pats :=
    lazymatch pats with
    | [] => idtac
    | SForall :: ?pats => try (iSpecializeArgs H1 (hcons _ _)); go H1 pats
    | SName ?H2 :: ?pats =>
       eapply tac_specialize with _ _ H2 _ H1 _ _ _ _; (* (j:=H1) (i:=H2) *)
         [env_cbv; reflexivity || fail "iSpecialize:" H2 "not found"
         |env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |let P := match goal with |- IntoWand ?P ?Q _ => P end in
          let Q := match goal with |- IntoWand ?P ?Q _ => Q end in
          apply _ || fail "iSpecialize: cannot instantiate" P "with" Q
         |env_cbv; reflexivity|go H1 pats]
    | SGoalPersistent :: ?pats =>
       eapply tac_specialize_assert_persistent with _ _ H1 _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- PersistentP ?Q => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity
         |(*goal*)
         |go H1 pats]
    | SGoalPure :: ?pats =>
       eapply tac_specialize_assert_pure with _ H1 _ _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- FromPure ?Q _ => Q end in
          apply _ || fail "iSpecialize:" Q "not pure"
         |env_cbv; reflexivity
         |(*goal*)
         |go H1 pats]
    | SGoal (SpecGoal ?vs ?lr ?Hs_frame ?Hs) :: ?pats =>
       eapply tac_specialize_assert with _ _ _ H1 _ lr (Hs_frame ++ Hs) _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |match vs with
          | false => apply into_assert_default
          | true => apply _ || fail "iSpecialize: cannot generate view shifted goal"
          end
         |env_cbv; reflexivity || fail "iSpecialize:" Hs "not found"
         |iFrame Hs_frame (*goal*)
         |go H1 pats]
    end in let pats := spec_pat.parse pat in go H pats.

(* p = whether the conclusion of the specialized term is persistent. It can
either be a Boolean or an introduction pattern, which will be coerced in true
when it only contains `#` or `%` patterns at the top-level. *)
Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) tactic(tac) :=
  let p :=
    lazymatch type of p with
    | intro_pat => eval cbv in (intro_pat_persistent p)
    | string =>
       let pat := intro_pat.parse_one p in
       eval cbv in (intro_pat_persistent pat)
    | _ => p
    end in
  lazymatch t with
  | ITrm ?H ?xs ?pat =>
    lazymatch p with
    | true =>
       eapply tac_specialize_persistent_helper with _ H _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H "not found"
         |iSpecializeArgs H xs; iSpecializePat H pat; last (iExact H)
         |let Q := match goal with |- PersistentP ?Q => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity|tac H]
    | false => iSpecializeArgs H xs; iSpecializePat H pat; last (tac H)
    end
  end.

Tactic Notation "iSpecialize" open_constr(t) :=
  iSpecializeCore t as false (fun _ => idtac).
Tactic Notation "iSpecialize" open_constr(t) "#" :=
  iSpecializeCore t as true (fun _ => idtac).

(** * Pose proof *)
(* The tactic [iIntoEntails] tactic solves a goal [True ⊢ Q]. The arguments [t]
is a Coq term whose type is of the following shape:

- [∀ (x_1 : A_1) .. (x_n : A_n), True ⊢ Q]
- [∀ (x_1 : A_1) .. (x_n : A_n), P1 ⊢ P2], in which case [Q] becomes [P1 -★ P2]
- [∀ (x_1 : A_1) .. (x_n : A_n), P1 ⊣⊢ P2], in which case [Q] becomes [P1 ↔ P2]

The tactic instantiates each dependent argument [x_i] with an evar and generates
a goal [P] for non-dependent arguments [x_i : P]. *)
Tactic Notation "iIntoEntails" open_constr(t) :=
  let rec go t :=
    let tT := type of t in
    lazymatch eval hnf in tT with
    | True ⊢ _ => apply t
    | _ ⊢ _ => apply (uPred.entails_wand _ _ t)
    (* need to use the unfolded version of [⊣⊢] due to the hnf *)
    | uPred_equiv' _ _ => apply (uPred.equiv_iff _ _ t)
    | ?P → ?Q => let H := fresh in assert P as H; [|go uconstr:(t H); clear H]
    | ∀ _ : ?T, _ =>
       (* Put [T] inside an [id] to avoid TC inference from being invoked. *)
       (* This is a workarround for Coq bug #4969. *)
       let e := fresh in evar (e:id T);
       let e' := eval unfold e in e in clear e; go (t e')
    end
  in go t.

Tactic Notation "iPoseProofCore" open_constr(lem) "as" constr(p) tactic(tac) :=
  let pose_trm t tac :=
    let Htmp := iFresh in
    lazymatch type of t with
    | string =>
       eapply tac_pose_proof_hyp with _ _ t _ Htmp _;
         [env_cbv; reflexivity || fail "iPoseProof:" t "not found"
         |env_cbv; reflexivity || fail "iPoseProof:" Htmp "not fresh"
         |tac Htmp]
    | _ =>
       eapply tac_pose_proof with _ Htmp _; (* (j:=H) *)
         [iIntoEntails t
         |env_cbv; reflexivity || fail "iPoseProof:" Htmp "not fresh"
         |tac Htmp]
    end;
    try (apply _) (* solve TC constraints. It is essential that this happens
    after the continuation [tac] has been called. *)
  in lazymatch lem with
  | ITrm ?t ?xs ?pat =>
     pose_trm t ltac:(fun Htmp => iSpecializeCore (ITrm Htmp xs pat) as p tac)
  | _ => pose_trm lem tac
  end.

Tactic Notation "iPoseProof" open_constr(lem) "as" constr(H) :=
  iPoseProofCore lem as false (fun Htmp => iRename Htmp into H).

(** * Apply *)
Tactic Notation "iApply" open_constr(lem) :=
  let finish H := first
    [iExact H
    |eapply tac_apply with _ H _ _ _;
       [env_cbv; reflexivity || fail 1 "iApply:" H "not found"
       |let P := match goal with |- IntoWand ?P _ _ => P end in
        apply _ || fail 1 "iApply: cannot apply" P
       |lazy beta (* reduce betas created by instantiation *)]] in
  lazymatch lem with
  | ITrm ?t ?xs ?pat =>
     iPoseProofCore t as false (fun Htmp =>
       iSpecializeArgs Htmp xs;
       try (iSpecializeArgs Htmp (hcons _ _));
       iSpecializePat Htmp pat; last finish Htmp)
  | _ =>
     iPoseProofCore lem as false (fun Htmp =>
       try (iSpecializeArgs Htmp (hcons _ _));
       finish Htmp)
  end.

(** * Revert *)
Local Tactic Notation "iForallRevert" ident(x) :=
  let A := type of x in
  lazymatch type of A with
  | Prop => revert x; apply tac_pure_revert
  | _ => revert x; apply tac_forall_revert
  end || fail "iRevert: cannot revert" x.

Tactic Notation "iRevert" constr(Hs) :=
  let rec go H2s :=
    match H2s with
    | [] => idtac
    | "★" :: ?H2s => go H2s; eapply tac_revert_spatial; env_cbv
    | ?H2 :: ?H2s =>
       go H2s;
       eapply tac_revert with _ H2 _ _; (* (i:=H2) *)
         [env_cbv; reflexivity || fail "iRevert:" H2 "not found"
         |env_cbv]
    end in
  let Hs := words Hs in go Hs.

Tactic Notation "iRevert" "(" ident(x1) ")" :=
  iForallRevert x1.
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" :=
  iForallRevert x2; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iForallRevert x3; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iForallRevert x4; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" :=
  iForallRevert x5; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" :=
  iForallRevert x6; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" :=
  iForallRevert x7; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iForallRevert x8; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).

Tactic Notation "iRevert" "(" ident(x1) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 ).

(** * Disjunction *)
Tactic Notation "iLeft" :=
  eapply tac_or_l;
    [let P := match goal with |- FromOr ?P _ _ => P end in
     apply _ || fail "iLeft:" P "not a disjunction"|].
Tactic Notation "iRight" :=
  eapply tac_or_r;
    [let P := match goal with |- FromOr ?P _ _ => P end in
     apply _ || fail "iRight:" P "not a disjunction"|].

Local Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with _ _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_cbv; reflexivity || fail "iOrDestruct:" H "not found"
    |let P := match goal with |- IntoOr ?P _ _ => P end in
     apply _ || fail "iOrDestruct: cannot destruct" P
    |env_cbv; reflexivity || fail "iOrDestruct:" H1 "not fresh"
    |env_cbv; reflexivity || fail "iOrDestruct:" H2 "not fresh"| |].

(** * Conjunction and separating conjunction *)
Tactic Notation "iSplit" :=
  lazymatch goal with
  | |- _ ⊢ _ =>
    eapply tac_and_split;
      [let P := match goal with |- FromAnd ?P _ _ => P end in
       apply _ || fail "iSplit:" P "not a conjunction"| |]
  | |- _ ⊣⊢ _ => apply (anti_symm (⊢))
  end.

Tactic Notation "iSplitL" constr(Hs) :=
  let Hs := words Hs in
  eapply tac_sep_split with _ _ false Hs _ _; (* (js:=Hs) *)
    [let P := match goal with |- FromSep ?P _ _ => P end in
     apply _ || fail "iSplitL:" P "not a separating conjunction"
    |env_cbv; reflexivity || fail "iSplitL: hypotheses" Hs
                                  "not found in the context"| |].
Tactic Notation "iSplitR" constr(Hs) :=
  let Hs := words Hs in
  eapply tac_sep_split with _ _ true Hs _ _; (* (js:=Hs) *)
    [let P := match goal with |- FromSep ?P _ _ => P end in
     apply _ || fail "iSplitR:" P "not a separating conjunction"
    |env_cbv; reflexivity || fail "iSplitR: hypotheses" Hs
                                  "not found in the context"| |].

Tactic Notation "iSplitL" := iSplitR "".
Tactic Notation "iSplitR" := iSplitL "".

Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_destruct with _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_cbv; reflexivity || fail "iAndDestruct:" H "not found"
    |let P := match goal with |- IntoAnd _ ?P _ _ => P end in
     apply _ || fail "iAndDestruct: cannot destruct" P
    |env_cbv; reflexivity || fail "iAndDestruct:" H1 "or" H2 " not fresh"|].

Local Tactic Notation "iAndDestructChoice" constr(H) "as" constr(lr) constr(H') :=
  eapply tac_and_destruct_choice with _ H _ lr H' _ _ _;
    [env_cbv; reflexivity || fail "iAndDestruct:" H "not found"
    |let P := match goal with |- IntoAnd _ ?P _ _ => P end in
     apply _ || fail "iAndDestruct: cannot destruct" P
    |env_cbv; reflexivity || fail "iAndDestruct:" H' " not fresh"|].

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(H) :=
  eapply tac_combine with _ _ _ H1 _ _ H2 _ _ H _;
    [env_cbv; reflexivity || fail "iCombine:" H1 "not found"
    |env_cbv; reflexivity || fail "iCombine:" H2 "not found"
    |let P1 := match goal with |- FromSep _ ?P1 _ => P1 end in
     let P2 := match goal with |- FromSep _ _ ?P2 => P2 end in
     apply _ || fail "iCombine: cannot combine" P1 "and" P2
    |env_cbv; reflexivity || fail "iCombine:" H "not fresh"|].

(** * Existential *)
Tactic Notation "iExists" uconstr(x1) :=
  eapply tac_exist;
    [let P := match goal with |- FromExist ?P _ => P end in
     apply _ || fail "iExists:" P "not an existential"
    |cbv beta; eexists x1].

Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) :=
  iExists x1; iExists x2.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) :=
  iExists x1; iExists x2, x3.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) :=
  iExists x1; iExists x2, x3, x4.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) :=
  iExists x1; iExists x2, x3, x4, x5.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) :=
  iExists x1; iExists x2, x3, x4, x5, x6.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) ","
    uconstr(x8) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7, x8.

Local Tactic Notation "iExistDestruct" constr(H)
    "as" simple_intropattern(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _; (* (i:=H) (j:=Hx) *)
    [env_cbv; reflexivity || fail "iExistDestruct:" H "not found"
    |let P := match goal with |- IntoExist ?P _ => P end in
     apply _ || fail "iExistDestruct: cannot destruct" P|];
  let y := fresh in
  intros y; eexists; split;
    [env_cbv; reflexivity || fail "iExistDestruct:" Hx "not fresh"
    |revert y; intros x].

(** * Always *)
Tactic Notation "iAlways":=
  apply tac_always_intro;
    [reflexivity || fail "iAlways: spatial context non-empty"|].

(** * Later *)
Tactic Notation "iNext":=
  eapply tac_next;
    [apply _
    |let P := match goal with |- FromLater ?P _ => P end in
     apply _ || fail "iNext:" P "does not contain laters"|].

Tactic Notation "iTimeless" constr(H) :=
  eapply tac_timeless with _ H _ _ _;
    [let Q := match goal with |- IsExceptLast ?Q => Q end in
     apply _ || fail "iTimeless: cannot remove later when goal is" Q
    |env_cbv; reflexivity || fail "iTimeless:" H "not found"
    |let P := match goal with |- IntoExceptLast ?P _ => P end in
     apply _ || fail "iTimeless: cannot turn" P "into ◇"
    |env_cbv; reflexivity|].

(** * View shifts *)
Tactic Notation "iVsIntro" :=
  eapply tac_vs_intro;
    [let P := match goal with |- FromVs ?P _ => P end in
     apply _ || fail "iVsIntro:" P "not a view shift"|].

Tactic Notation "iVsCore" constr(H) :=
  eapply tac_vs_elim with _ H _ _ _ _;
    [env_cbv; reflexivity || fail "iVs:" H "not found"
    |let P := match goal with |- ElimVs ?P _ _ _ => P end in
     let Q := match goal with |- ElimVs _ _ ?Q _ => Q end in
     apply _ || fail "iVs: cannot run" P "in" Q
                     "because the goal or hypothesis is not a view shift"
    |env_cbv; reflexivity|].

(** * Basic destruct tactic *)
Local Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  let rec go Hz pat :=
    lazymatch pat with
    | IAnom => idtac
    | IDrop => iClear Hz
    | IFrame => iFrame Hz
    | IName ?y => iRename Hz into y
    | IList [[]] => iExFalso; iExact Hz
    | IList [[?pat1; IDrop]] => iAndDestructChoice Hz as true Hz; go Hz pat1
    | IList [[IDrop; ?pat2]] => iAndDestructChoice Hz as false Hz; go Hz pat2
    | IList [[?pat1; ?pat2]] =>
       let Hy := iFresh in iAndDestruct Hz as Hz Hy; go Hz pat1; go Hy pat2
    | IList [[?pat1];[?pat2]] => iOrDestruct Hz as Hz Hz; [go Hz pat1|go Hz pat2]
    | IPureElim => iPure Hz as ?
    | IAlwaysElim ?pat => iPersistent Hz; go Hz pat
    | ILaterElim ?pat => iTimeless Hz; go Hz pat
    | IVsElim ?pat => iVsCore Hz; go Hz pat
    | _ => fail "iDestruct:" pat "invalid"
    end
  in let pat := intro_pat.parse_one pat in go H pat.

Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as @ pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat.
Local Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat.

(** * Introduction tactic *)
Local Tactic Notation "iIntro" "(" simple_intropattern(x) ")" := first
  [ (* (∀ _, _) *) apply tac_forall_intro; intros x
  | (* (?P → _) *) eapply tac_impl_intro_pure;
     [let P := match goal with |- IntoPure ?P _ => P end in
      apply _ || fail "iIntro:" P "not pure"
     |intros x]
  | (* (?P -★ _) *) eapply tac_wand_intro_pure;
     [let P := match goal with |- IntoPure ?P _ => P end in
      apply _ || fail "iIntro:" P "not pure"
     |intros x]
  |intros x].

Local Tactic Notation "iIntro" constr(H) := first
  [ (* (?Q → _) *)
    eapply tac_impl_intro with _ H; (* (i:=H) *)
      [reflexivity || fail 1 "iIntro: introducing" H
                             "into non-empty spatial context"
      |env_cbv; reflexivity || fail "iIntro:" H "not fresh"|]
  | (* (_ -★ _) *)
    eapply tac_wand_intro with _ H; (* (i:=H) *)
      [env_cbv; reflexivity || fail 1 "iIntro:" H "not fresh"|]
  | fail 1 "iIntro: nothing to introduce" ].

Local Tactic Notation "iIntro" "#" constr(H) := first
  [ (* (?P → _) *)
    eapply tac_impl_intro_persistent with _ H _; (* (i:=H) *)
      [let P := match goal with |- IntoPersistentP ?P _ => P end in
       apply _ || fail 1 "iIntro: " P " not persistent"
      |env_cbv; reflexivity || fail 1 "iIntro:" H "not fresh"|]
  | (* (?P -★ _) *)
    eapply tac_wand_intro_persistent with _ H _; (* (i:=H) *)
      [let P := match goal with |- IntoPersistentP ?P _ => P end in
       apply _ || fail 1 "iIntro: " P " not persistent"
      |env_cbv; reflexivity || fail 1 "iIntro:" H "not fresh"|]
  | fail 1 "iIntro: nothing to introduce" ].

Local Tactic Notation "iIntroForall" :=
  lazymatch goal with
  | |- ∀ _, ?P => fail
  | |- ∀ _, _ => intro
  | |- _ ⊢ (∀ x : _, _) => iIntro (x)
  end.
Local Tactic Notation "iIntro" :=
  lazymatch goal with
  | |- _ → ?P => intro
  | |- _ ⊢ (_ -★ _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
  | |- _ ⊢ (_ → _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
  end.

Tactic Notation "iIntros" constr(pat) :=
  let rec go pats :=
    lazymatch pats with
    | [] => idtac
    | IPureElim :: ?pats => iIntro (?); go pats
    | IAlwaysElim IAnom :: ?pats => let H := iFresh in iIntro #H; go pats
    | IAnom :: ?pats => let H := iFresh in iIntro H; go pats
    | IAlwaysElim (IName ?H) :: ?pats => iIntro #H; go pats
    | IName ?H :: ?pats => iIntro H; go pats
    | IPureIntro :: ?pats => iPureIntro; go pats
    | IAlwaysIntro :: ?pats => iAlways; go pats
    | ILaterIntro :: ?pats => iNext; go pats
    | IVsIntro :: ?pats => iVsIntro; go pats
    | ISimpl :: ?pats => simpl; go pats
    | IForall :: ?pats => repeat iIntroForall; go pats
    | IAll :: ?pats => repeat (iIntroForall || iIntro); go pats
    | IClear ?cpats :: ?pats =>
       let rec clr cpats :=
         match cpats with
         | [] => go pats
         | (false,?H) :: ?cpats => iClear H; clr cpats
         | (true,?H) :: ?cpats => iFrame H; clr cpats
         end in clr cpats
    | IAlwaysElim ?pat :: ?pats =>
       let H := iFresh in iIntro #H; iDestructHyp H as pat; go pats
    | ?pat :: ?pats =>
       let H := iFresh in iIntro H; iDestructHyp H as pat; go pats
    end
  in let pats := intro_pat.parse pat in try iProof; go pats.
Tactic Notation "iIntros" := iIntros [IAll].

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" :=
  try iProof; iIntro ( x1 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" :=
  iIntros ( x1 ); iIntro ( x2 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" :=
  iIntros ( x1 x2 ); iIntro ( x3 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" :=
  iIntros ( x1 x2 x3 ); iIntro ( x4 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) ")" :=
  iIntros ( x1 x2 x3 x4 ); iIntro ( x5 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntro ( x6 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntro ( x7 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntro ( x8 ).

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" constr(p) :=
  iIntros ( x1 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    ")" constr(p) :=
  iIntros ( x1 x2 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" constr(p) :=
  iIntros ( x1 x2 x3 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntros p.
Tactic Notation "iIntros" "("simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p.

Tactic Notation "iRevertIntros" "with" tactic(tac) :=
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := eval cbv in (reverse (env_dom (env_spatial Δ))) in
     iRevert ["★"]; tac; iIntros Hs
  end.
Tactic Notation "iRevertIntros" "(" ident(x1) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1); tac; iIntros (x1)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2); tac; iIntros (x1 x2)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")"
    "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3); tac; iIntros (x1 x2 x3)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3 x4); tac; iIntros (x1 x2 x3 x4)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3 x4 x5); tac; iIntros (x1 x2 x3 x4 x5)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3 x4 x5 x6);
    tac; iIntros (x1 x2 x3 x4 x5 x6)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3 x4 x5 x6 x7);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" "with" tactic(tac):=
  iRevertIntros with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8)).

(** * Destruct tactic *)
Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic(tac) :=
  let intro_destruct n :=
    let rec go n' :=
      lazymatch n' with
      | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
      | 1 => repeat iIntroForall; let H := iFresh in iIntro H; tac H
      | S ?n' => repeat iIntroForall; let H := iFresh in iIntro H; go n'
      end in intros; try iProof; go n in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z => (* to make it work in Z_scope. We should just be able to bind
     tactic notation arguments to notation scopes. *)
     let n := eval compute in (Z.to_nat lem) in intro_destruct n
  | string => tac lem
  | iTrm =>
     (* only copy the hypothesis when universal quantifiers are instantiated *)
     lazymatch lem with
     | @iTrm string ?H _ hnil ?pat => iSpecializeCore lem as p tac
     | _ => iPoseProofCore lem as p tac
     end
  | _ => iPoseProofCore lem as p tac
  end.

Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as true (fun H => iPure H as pat).

(** * Induction *)
Tactic Notation "iInductionCore" constr(x)
    "as" simple_intropattern(pat) constr(IH) :=
  let rec fix_ihs :=
    lazymatch goal with
    | H : coq_tactics.of_envs _ ⊢ _ |- _ =>
       eapply tac_revert_ih;
         [env_cbv; reflexivity
         |apply H|];
       clear H; fix_ihs;
       let IH' := iFresh' IH in iIntros [IAlwaysElim (IName IH')]
    | _ => idtac
    end in
  induction x as pat; fix_ihs.

Tactic Notation "iInduction" constr(x)
    "as" simple_intropattern(pat) constr(IH) :=
  iRevertIntros with (iInductionCore x as pat IH).

(** * Löb Induction *)
Tactic Notation "iLöbCore" "as" constr (IH) :=
  eapply tac_löb with _ IH;
    [reflexivity
    |env_cbv; reflexivity || fail "iLöb:" IH "not fresh"|].

Tactic Notation "iLöb" "as" constr (IH) :=
  iRevertIntros with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ")" "as" constr (IH) :=
  iRevertIntros(x1) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2 x3) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" "as"
    constr (IH):=
  iRevertIntros(x1 x2 x3 x4) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2 x3 x4 x5) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2 x3 x4 x5 x6) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2 x3 x4 x5 x6 x7) with (iLöbCore as IH).
Tactic Notation "iLöb" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" "as" constr (IH) :=
  iRevertIntros(x1 x2 x3 x4 x5 x6 x7 x8) with (iLöbCore as IH).

(** * Assert *)
Tactic Notation "iAssertCore" open_constr(Q) "with" constr(Hs) "as" tactic(tac) :=
  let H := iFresh in
  let Hs := spec_pat.parse Hs in
  lazymatch Hs with
  | [SGoalPersistent] =>
     eapply tac_assert_persistent with _ H Q;
       [env_cbv; reflexivity
       |(*goal*)
       |apply _ || fail "iAssert:" Q "not persistent"
       |tac H]
  | [SGoal (SpecGoal ?vs ?lr ?Hs_frame ?Hs)] =>
     eapply tac_assert with _ _ _ lr (Hs_frame ++ Hs) H Q _;
       [match vs with
        | false => apply into_assert_default
        | true => apply _ || fail "iAssert: cannot generate view shifted goal"
        end
       |env_cbv; reflexivity || fail "iAssert:" Hs "not found"
       |env_cbv; reflexivity
       |iFrame Hs_frame (*goal*)
       |tac H]
  | ?pat => fail "iAssert: invalid pattern" pat
  end.

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as" constr(pat) :=
  iAssertCore Q with Hs as (fun H => iDestructHyp H as pat).
Tactic Notation "iAssert" open_constr(Q) "as" constr(pat) :=
  iAssert Q with "[]" as pat.

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs)
    "as" "%" simple_intropattern(pat) :=
  iAssertCore Q with Hs as (fun H => iPure H as pat).
Tactic Notation "iAssert" open_constr(Q) "as" "%" simple_intropattern(pat) :=
  iAssert Q with "[]" as %pat.

(** * Rewrite *)
Local Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite _ Heq _ _ lr);
      [env_cbv; reflexivity || fail "iRewrite:" Heq "not found"
      |let P := match goal with |- ?P ⊢ _ => P end in
       reflexivity || fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity|lazy beta; iClear Heq]).

Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore false lem.
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore true lem.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
      [env_cbv; reflexivity || fail "iRewrite:" Heq "not found"
      |env_cbv; reflexivity || fail "iRewrite:" H "not found"
      |let P := match goal with |- ?P ⊢ _ => P end in
       reflexivity || fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity
      |env_cbv; reflexivity|lazy beta; iClear Heq]).

Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) :=
  iRewriteCore false lem in H.
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
  iRewriteCore true lem in H.

Ltac iSimplifyEq := repeat (
  iMatchGoal ltac:(fun H P => match P with (_ = _)%I => iDestruct H as %? end)
  || simplify_eq/=).

(** * View shifts *)
Tactic Notation "iVs" open_constr(lem) :=
  iDestructCore lem as false (fun H => iVsCore H).
Tactic Notation "iVs" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as false (fun H => iVsCore H; last iDestructHyp H as pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H => iVsCore H; last iDestructHyp H as ( x1 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iVsCore H; last iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iVsCore H; last iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iVsCore H; last iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iVsCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iVsCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iVsCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iVs" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iVsCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "iVs" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as false (fun H => iVsCore H; iPure H as pat).

(* Make sure that by and done solve trivial things in proof mode *)
Hint Extern 0 (of_envs _ ⊢ _) => by iPureIntro.
Hint Extern 0 (of_envs _ ⊢ _) => iAssumption.
Hint Extern 0 (of_envs _ ⊢ _) => progress iIntros.
Hint Resolve uPred.eq_refl'. (* Maybe make an [iReflexivity] tactic *)

(* We should be able to write [Hint Extern 1 (of_envs _ ⊢ (_ ★ _)%I) => ...],
but then [eauto] mysteriously fails. See bug 4762 *)
Hint Extern 1 (of_envs _ ⊢ _) =>
  match goal with
  | |- _ ⊢ _ ∧ _ => iSplit
  | |- _ ⊢ _ ★ _ => iSplit
  | |- _ ⊢ ▷ _ => iNext
  | |- _ ⊢ □ _ => iClear "*"; iAlways
  | |- _ ⊢ ∃ _, _ => iExists _
  | |- _ ⊢ |=r=> _ => iVsIntro
  end.
Hint Extern 1 (of_envs _ ⊢ _) =>
  match goal with |- _ ⊢ (_ ∨ _)%I => iLeft end.
Hint Extern 1 (of_envs _ ⊢ _) =>
  match goal with |- _ ⊢ (_ ∨ _)%I => iRight end.
