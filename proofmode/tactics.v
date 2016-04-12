From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.algebra Require Export upred.
From iris.proofmode Require Export notation.
From iris.prelude Require Import stringmap.

Declare Reduction env_cbv := cbv [
  env_lookup env_fold env_lookup_delete env_delete env_app
    env_replace env_split_go env_split
  decide (* operational classes *)
  sumbool_rec sumbool_rect (* sumbool *)
  bool_eq_dec bool_rec bool_rect bool_dec eqb andb (* bool *)
  assci_eq_dec ascii_to_digits Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  string_eq_dec string_rec string_rect (* strings *)
  env_persistent env_spatial envs_persistent
  envs_lookup envs_lookup_delete envs_delete envs_app
    envs_simple_replace envs_replace envs_split envs_clear_spatial].
Ltac env_cbv :=
  match goal with |- ?u => let v := eval env_cbv in u in change v end.

Ltac iFresh :=
  lazymatch goal with
  |- of_envs ?Δ ⊢ _ =>
      match goal with
      | _ => eval vm_compute in (fresh_string_of_set "~" (dom stringset Δ))
      | _ => eval cbv in (fresh_string_of_set "~" (dom stringset Δ))
      end
  | _ => constr:"~"
  end.

(** * Misc *)
Tactic Notation "iTypeOf" constr(H) tactic(tac):=
  let Δ := match goal with |- of_envs ?Δ ⊢ _ => Δ end in
  match eval env_cbv in (envs_lookup H Δ) with
  | Some (?p,?P) => tac p P
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
    | ?H :: ?Hs =>
       eapply tac_clear with _ H _ _; (* (i:=H) *)
         [env_cbv; reflexivity || fail "iClear:" H "not found"|go Hs]
    end in
  let Hs := words Hs in go Hs.

Tactic Notation "iClear" "★" :=
  eapply tac_clear_spatial; [env_cbv; reflexivity|].

(** * Assumptions *)
Tactic Notation "iExact" constr(H) :=
  eapply tac_exact with H _; (* (i:=H) *)
    env_cbv;
    lazymatch goal with
    | |- None = Some _ => fail "iExact:" H "not found"
    | |- Some (_, ?P) = Some _ =>
       reflexivity || fail "iExact:" H ":" P "does not match goal"
    end.

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
  eapply tac_exact; iAssumptionCore;
  match goal with |- _ = Some (_, ?P) => fail "iAssumption:" P "not found" end.

(** * False *)
Tactic Notation "iExFalso" := apply tac_ex_falso.
Tactic Notation "iContradiction" constr(H) := iExFalso; iExact H.
Tactic Notation "iContradiction" := iExFalso; iAssumption.

(** * Pure introduction *)
Tactic Notation "iIntro" "{" simple_intropattern(x) "}" :=
  lazymatch goal with
  | |- _ ⊢ (∀ _, _) => apply tac_forall_intro; intros x
  | |- _ ⊢ (?P → _) =>
     eapply tac_impl_intro_pure;
       [apply _ || fail "iIntro:" P "not pure"|]; intros x
  | |- _ ⊢ (?P -★ _) =>
     eapply tac_wand_intro_pure;
       [apply _ || fail "iIntro:" P "not pure"|]; intros x
  | |- _ => intros x
  end.

(** * Introduction *)
Tactic Notation "iIntro" constr(H) :=
  lazymatch goal with
  | |- _ ⊢ (?Q → _) =>
    eapply tac_impl_intro with _ H; (* (i:=H) *)
      [reflexivity || fail "iIntro: introducing " H ":" Q
                           "into non-empty spatial context"
      |env_cbv; reflexivity || fail "iIntro:" H "not fresh"|]
  | |- _ ⊢ (_ -★ _) =>
    eapply tac_wand_intro with _ H; (* (i:=H) *)
      [env_cbv; reflexivity || fail "iIntro:" H "not fresh"|]
  | _ => fail "iIntro: nothing to introduce"
  end.

Tactic Notation "iIntro" "#" constr(H) :=
  lazymatch goal with
  | |- _ ⊢ (?P → _) =>
    eapply tac_impl_intro_persistent with _ H _; (* (i:=H) *)
      [apply _ || fail "iIntro: " P " not persistent"
      |env_cbv; reflexivity || fail "iIntro:" H "not fresh"|]
  | |- _ ⊢ (?P -★ _) =>
    eapply tac_wand_intro_persistent with _ H _; (* (i:=H) *)
      [apply _ || fail "iIntro: " P " not persistent"
      |env_cbv; reflexivity || fail "iIntro:" H "not fresh"|]
  | _ => fail "iIntro: nothing to introduce"
  end.

(** * Making hypotheses persistent or pure *)
Tactic Notation "iPersistent" constr(H) :=
  eapply tac_persistent with _ H _ _ _; (* (i:=H) *)
    [env_cbv; reflexivity || fail "iPersistent:" H "not found"
    |let Q := match goal with |- ToPersistentP ?Q _ => Q end in
     apply _ || fail "iPersistent:" H ":" Q "not persistent"
    |env_cbv; reflexivity|].

Tactic Notation "iDuplicate" constr(H1) "as" constr(H2) :=
  eapply tac_duplicate with _ H1 _ H2 _; (* (i:=H1) (j:=H2) *)
    [env_cbv; reflexivity || fail "iDuplicate:" H1 "not found"
    |reflexivity || fail "iDuplicate:" H1 "not in persistent context"
    |env_cbv; reflexivity || fail "iDuplicate:" H2 "not fresh"|].
Tactic Notation "iDuplicate" "#" constr(H1) "as" constr(H2) :=
  iPersistent H1; iDuplicate H1 as H2.

Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with _ H _ _ _; (* (i:=H1) *)
    [env_cbv; reflexivity || fail "iPure:" H "not found"
    |let P := match goal with |- ToPure ?P _ => P end in
     apply _ || fail "iPure:" H ":" P "not pure"
    |intros pat].
Tactic Notation "iPure" constr(H) := iPure H as ?.

Tactic Notation "iPureIntro" := apply uPred.const_intro.

(** * Specialize *)
Tactic Notation "iForallSpecialize" constr(H) open_constr(x) :=
  eapply tac_forall_specialize with _ H _ _ x; (* (i:=H) (a:=x) *)
    [env_cbv; reflexivity || fail "iSpecialize:" H "not found"
    |env_cbv; reflexivity|].

Tactic Notation "iSpecialize" constr (H) constr(pat) :=
  let solve_to_wand H1 :=
    let P := match goal with |- ToWand ?P _ _ => P end in
    apply _ || fail "iSpecialize:" H1 ":" P "not an implication/wand" in
  let rec go H1 pats :=
    lazymatch pats with
    | [] => idtac
    | SAlways :: ?pats => iPersistent H1; go H1 pats
    | SSplit true [] :: SAlways :: ?pats =>
       eapply tac_specialize_domain_persistent with _ _ H1 _ _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- ToPersistentP ?Q _ => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity
         | |go H1 pats]
    | SName ?H2 :: SAlways :: ?pats =>
       eapply tac_specialize_domain_persistent with _ _ H1 _ _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- ToPersistentP ?Q _ => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity
         |iExact H2 || fail "iSpecialize:" H2 "not found or wrong type"
         |go H1 pats]
    | SName ?H2 :: ?pats =>
       eapply tac_specialize with _ _ H2 _ H1 _ _ _ _; (* (j:=H1) (i:=H2) *)
         [env_cbv; reflexivity || fail "iSpecialize:" H2 "not found"
         |env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |env_cbv; reflexivity|go H1 pats]
    | SPersistent :: ?pats =>
       eapply tac_specialize_range_persistent with _ _ H1 _ _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- PersistentP ?Q => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity| |go H1 pats]
    | SPure :: ?pats =>
       eapply tac_specialize_range_persistent with _ _ H1 _ _ _ _; (* make custom tac_ lemma *)
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |let Q := match goal with |- PersistentP ?Q => Q end in
          apply _ || fail "iSpecialize:" Q "not persistent"
         |env_cbv; reflexivity|iPureIntro|go H1 pats]
    | SSplit ?lr ?Hs :: ?pats =>
       eapply tac_specialize_assert with _ _ _ H1 _ lr Hs _ _ _;
         [env_cbv; reflexivity || fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |env_cbv; reflexivity || fail "iSpecialize:" Hs "not found"|
         |go H1 pats]
    end in
  repeat (iForallSpecialize H _);
  let pats := spec_pat.parse pat in go H pats.

Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) "}" :=
  iForallSpecialize H x1.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1)
    open_constr(x2) "}" :=
  iSpecialize H { x1 }; iForallSpecialize H x2.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) "}" :=
  iSpecialize H { x1 x2 }; iForallSpecialize H x3.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) "}" :=
  iSpecialize H { x1 x2 x3 }; iForallSpecialize H x4.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
     open_constr(x3) open_constr(x4) open_constr(x5) "}" :=
  iSpecialize H { x1 x2 x3 x4 }; iForallSpecialize H x5.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 }; iForallSpecialize H x6.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 }; iForallSpecialize H x7.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) open_constr(x8) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 }; iForallSpecialize H x8.

Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) "}" constr(Hs) :=
  iSpecialize H { x1 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2) "}"
    constr(Hs) :=
  iSpecialize H { x1 x2 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6) "}"
    constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 }; iSpecialize H @ Hs.
Tactic Notation "iSpecialize" constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) open_constr(x8) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 x8 }; iSpecialize H @ Hs.

(** * Pose proof *)
Tactic Notation "iPoseProof" open_constr(lem) "as" constr(H) :=
  eapply tac_pose_proof with _ H _; (* (j:=H) *)
    [first
       [eapply lem
       |apply uPred.entails_impl; eapply lem
       |apply uPred.equiv_iff; eapply lem]
    |env_cbv; reflexivity || fail "iPoseProof:" H "not fresh"|].

Tactic Notation "iPoseProof" open_constr(lem) constr(Hs) "as" constr(H) :=
  iPoseProof lem as H; last iSpecialize H Hs.

Tactic Notation "iPoseProof" open_constr(lem) :=
  let H := iFresh in iPoseProof lem as H.
Tactic Notation "iPoseProof" open_constr(lem) constr(Hs) :=
  let H := iFresh in iPoseProof lem Hs as H.

Tactic Notation "iPoseProof" open_constr(lem) "as" tactic(tac) :=
  lazymatch type of lem with
  | string => tac lem
  | _ => let H := iFresh in iPoseProof lem as H; last tac H; try apply _
  end.

Tactic Notation "iPoseProof" open_constr(lem) constr(Hs) "as" tactic(tac) :=
  iPoseProof lem as (fun H => iSpecialize H Hs; last tac H).

(** * Apply *)
Tactic Notation "iApply" open_constr (lem) :=
  iPoseProof lem as (fun H => repeat (iForallSpecialize H _); first
    [iExact H
    |eapply tac_apply with _ H _ _ _;
       [env_cbv; reflexivity || fail "iApply:" lem "not found"
       |apply _ || fail "iApply: cannot apply" lem|]]).
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) "}" :=
  iSpecialize H { x1 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1)
    open_constr(x2) "}" :=
  iSpecialize H { x1 x2 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) "}" :=
  iSpecialize H { x1 x2 x3 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) "}" :=
  iSpecialize H { x1 x2 x3 x4 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
     open_constr(x3) open_constr(x4) open_constr(x5) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 }; last iApply H.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) open_constr(x8) "}" :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 x8 }; last iApply H.

(* this is wrong *)
Tactic Notation "iApply" open_constr (lem) constr(Hs) :=
  iPoseProof lem Hs as (fun H => first
    [iExact H
    |eapply tac_apply with _ H _ _ _;
       [env_cbv; reflexivity || fail "iApply:" lem "not found"
       |apply _ || fail "iApply: cannot apply" lem|]]).
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) "}" constr(Hs) :=
  iSpecialize H { x1 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2) "}"
    constr(Hs) :=
  iSpecialize H { x1 x2 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6) "}"
    constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 }; last iApply H Hs.
Tactic Notation "iApply" open_constr (H) "{" open_constr(x1) open_constr(x2)
    open_constr(x3) open_constr(x4) open_constr(x5) open_constr(x6)
    open_constr(x7) open_constr(x8) "}" constr(Hs) :=
  iSpecialize H { x1 x2 x3 x4 x5 x6 x7 x8 }; last iApply H Hs.

(** * Revert *)
Tactic Notation "iRevert" "★" := eapply tac_revert_spatial; env_cbv.

Tactic Notation "iForallRevert" ident(x) :=
  match type of x with
  | _ : Prop => revert x; apply tac_pure_revert
  | _ => revert x; apply tac_forall_revert
  end.

Tactic Notation "iImplRevert" constr(H) :=
  eapply tac_revert with _ H _ _; (* (i:=H) *)
    [env_cbv; reflexivity || fail "iRevert:" H "not found"
    |env_cbv].

Tactic Notation "iRevert" constr(Hs) :=
  let rec go H2s :=
    match H2s with [] => idtac | ?H2 :: ?H2s => go H2s; iImplRevert H2 end in
  let Hs := words Hs in go Hs.

Tactic Notation "iRevert" "{" ident(x1) "}" :=
  iForallRevert x1.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) "}" :=
  iForallRevert x2; iRevert { x1 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) "}" :=
  iForallRevert x3; iRevert { x1 x2 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4) "}" :=
  iForallRevert x4; iRevert { x1 x2 x3 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) "}" :=
  iForallRevert x5; iRevert { x1 x2 x3 x4 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) "}" :=
  iForallRevert x6; iRevert { x1 x2 x3 x4 x5 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) "}" :=
  iForallRevert x7; iRevert { x1 x2 x3 x4 x5 x6 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) "}" :=
  iForallRevert x8; iRevert { x1 x2 x3 x4 x5 x6 x7 }.

Tactic Notation "iRevert" "{" ident(x1) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4) "}"
    constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 x4 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 x4 x5 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 x4 x5 x6 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 x4 x5 x6 x7 }.
Tactic Notation "iRevert" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) "}" constr(Hs) :=
  iRevert Hs; iRevert { x1 x2 x3 x4 x5 x6 x7 x8 }.

(** * Disjunction *)
Tactic Notation "iLeft" :=
  eapply tac_or_l;
    [let P := match goal with |- OrSplit ?P _ _ => P end in
     apply _ || fail "iLeft:" P "not a disjunction"|].
Tactic Notation "iRight" :=
  eapply tac_or_r;
    [let P := match goal with |- OrSplit ?P _ _ => P end in
     apply _ || fail "iRight:" P "not a disjunction"|].

Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with _ _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_cbv; reflexivity || fail "iOrDestruct:" H "not found"
    |let P := match goal with |- OrDestruct ?P _ _ => P end in
     apply _ || fail "iOrDestruct:" H ":" P "not a disjunction"
    |env_cbv; reflexivity || fail "iOrDestruct:" H1 "not fresh"
    |env_cbv; reflexivity || fail "iOrDestruct:" H2 "not fresh"| |].

(** * Conjunction and separating conjunction *)
Tactic Notation "iSplit" :=
  eapply tac_and_split;
    [let P := match goal with |- AndSplit ?P _ _ => P end in
     apply _ || fail "iSplit:" P "not a conjunction"| |].

Tactic Notation "iSplitL" constr(Hs) :=
  let Hs := words Hs in
  eapply tac_sep_split with _ _ false Hs _ _; (* (js:=Hs) *)
    [let P := match goal with |- SepSplit ?P _ _ => P end in
     apply _ || fail "iSplitL:" P "not a separating conjunction"
    |env_cbv; reflexivity || fail "iSplitL: hypotheses" Hs "not found"| |].
Tactic Notation "iSplitR" constr(Hs) :=
  let Hs := words Hs in
  eapply tac_sep_split with _ _ true Hs _ _; (* (js:=Hs) *)
    [let P := match goal with |- SepSplit ?P _ _ => P end in
     apply _ || fail "iSplitR:" P "not a separating conjunction"
    |env_cbv; reflexivity || fail "iSplitR: hypotheses" Hs "not found"| |].

Tactic Notation "iSplitL" := iSplitR "".
Tactic Notation "iSplitR" := iSplitL "".

Tactic Notation "iSepDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_sep_destruct with _ H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [env_cbv; reflexivity || fail "iSepDestruct:" H "not found"
    |let P := match goal with |- SepDestruct _ ?P _ _ => P end in
     apply _ || fail "iSepDestruct:" H ":" P "not separating destructable"
    |env_cbv; reflexivity || fail "iSepDestruct:" H1 "or" H2 " not fresh"|].

Tactic Notation "iFrame" constr(Hs) :=
  let rec go Hs :=
    match Hs with
    | [] => idtac
    | ?H :: ?Hs =>
       eapply tac_frame with _ H _ _ _;
         [env_cbv; reflexivity || fail "iFrame:" H "not found"
         |let R := match goal with |- Frame ?R _ _ => R end in
          apply _ || fail "iFrame: cannot frame" R
         |lazy iota beta; go Hs]
    end
  in let Hs := words Hs in go Hs.

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(H) :=
  eapply tac_combine with _ _ _ H1 _ _ H2 _ _ H _;
    [env_cbv; reflexivity || fail "iCombine:" H1 "not found"
    |env_cbv; reflexivity || fail "iCombine:" H2 "not found"
    |let P1 := match goal with |- SepSplit _ ?P1 _ => P1 end in
     let P2 := match goal with |- SepSplit _ _ ?P2 => P2 end in
     apply _ || fail "iCombine: cannot combine" H1 ":" P1 "and" H2 ":" P2
    |env_cbv; reflexivity || fail "iCombine:" H "not fresh"|].

(** * Existential *)
Tactic Notation "iExists" open_constr(x1) :=
  eapply tac_exist with _ x1 ;
    [let P := match goal with |- ExistSplit ?P _ => P end in
     apply _ || fail "iExists:" P "not an existential"
    |cbv beta].

Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) :=
  iExists x1; iExists x2.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) :=
  iExists x1; iExists x2, x3.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) "," open_constr(x4) :=
  iExists x1; iExists x2, x3, x4.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) "," open_constr(x4) "," open_constr(x5) :=
  iExists x1; iExists x2, x3, x4, x5.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) "," open_constr(x4) "," open_constr(x5) ","
    open_constr(x6) :=
  iExists x1; iExists x2, x3, x4, x5, x6.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) "," open_constr(x4) "," open_constr(x5) ","
    open_constr(x6) "," open_constr(x7) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7.
Tactic Notation "iExists" open_constr(x1) "," open_constr(x2) ","
    open_constr(x3) "," open_constr(x4) "," open_constr(x5) ","
    open_constr(x6) "," open_constr(x7) "," open_constr(x8) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7, x8.

Tactic Notation "iExistDestruct" constr(H) "as" ident(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _; (* (i:=H) (j:=Hx) *)
    [env_cbv; reflexivity || fail "iExistDestruct:" H "not found"
    |let P := match goal with |- ExistDestruct ?P _ => P end in
     apply _ || fail "iExistDestruct:" H ":" P "not an existential"|];
  intros x; eexists; split;
    [env_cbv; reflexivity || fail "iExistDestruct:" Hx "not fresh"|].

(** * Destruct tactic *)
Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  let rec go Hz pat :=
    lazymatch pat with
    | IAnom => idtac
    | IAnomPure => iPure Hz
    | IClear => iClear Hz
    | IName ?y => iRename Hz into y
    | IPersistent ?pat => iPersistent Hz; go Hz pat
    | IList [[]] => iContradiction Hz
    | IList [[?pat1; ?pat2]] =>
       let Hy := iFresh in iSepDestruct Hz as Hz Hy; go Hz pat1; go Hy pat2
    | IList [[?pat1];[?pat2]] => iOrDestruct Hz as Hz Hz; [go Hz pat1|go Hz pat2]
    | _ => fail "iDestruct:" pat "invalid"
    end
  in let pat := intro_pat.parse_one pat in go H pat.

Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1) "}"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as @ pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) "}" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) "}"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 x4 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) "}" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 x4 x5 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) "}" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 x4 x5 x6 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) "}"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 x4 x5 x6 x7 } pat.
Tactic Notation "iDestructHyp" constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) "}" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as { x2 x3 x4 x5 x6 x7 x8 } pat.

Tactic Notation "iDestruct" open_constr(H) "as" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1) "}"
    constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) "}" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) "}"
    constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 x4 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) "}" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 x4 x5 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) "}" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 x4 x5 x6 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) "}"
    constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 x4 x5 x6 x7 } pat).
Tactic Notation "iDestruct" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) "}" constr(pat) :=
  iPoseProof H as (fun H => iDestructHyp H as { x1 x2 x3 x4 x5 x6 x7 x8 } pat).

Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs; last iDestructHyp H as pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) "}"
    constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 x4 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 x4 x5 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6) "}"
    constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 x4 x5 x6 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 x4 x5 x6 x7 } pat).
Tactic Notation "iDestruct" open_constr(lem) constr(Hs) "as" "{"
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x8) "}" constr(pat) :=
  iPoseProof lem as (fun H => iSpecialize H Hs;
    last iDestructHyp H as { x1 x2 x3 x4 x5 x6 x7 x8 } pat).

Tactic Notation "iDestruct" open_constr(H) "as" "%" simple_intropattern(pat) :=
  let Htmp := iFresh in iDestruct H as Htmp; iPure Htmp as pat.
Tactic Notation "iDestruct" open_constr(H) constr(Hs)
    "as" "%" simple_intropattern(pat) :=
  let Htmp := iFresh in iDestruct H Hs as Htmp; iPure Htmp as pat.

(** * Always *)
Tactic Notation "iAlways":=
   apply tac_always_intro;
     [reflexivity || fail "iAlways: spatial context non-empty"|].

(** * Introduction tactic *)
Tactic Notation "iIntros" constr(pat) :=
  let rec go pats :=
    lazymatch pats with
    | [] => idtac
    | ISimpl :: ?pats => simpl; go pats
    | IAlways :: ?pats => iAlways; go pats
    | IPersistent (IName ?H) :: ?pats => iIntro #H; go pats
    | IName ?H :: ?pats => iIntro H; go pats
    | IPersistent IAnom :: ?pats => let H := iFresh in iIntro #H; go pats
    | IAnom :: ?pats => let H := iFresh in iIntro H; go pats
    | IAnomPure :: ?pats => iIntro {?}; go pats
    | IPersistent ?pat :: ?pats =>
       let H := iFresh in iIntro #H; iDestructHyp H as pat; go pats
    | ?pat :: ?pats =>
       let H := iFresh in iIntro H; iDestructHyp H as pat; go pats
    | _ => fail "iIntro: failed with" pats
    end
  in let pats := intro_pat.parse pat in try iProof; go pats.

Tactic Notation "iIntros" "{" simple_intropattern(x1) "}" :=
  try iProof; iIntro { x1 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" :=
  iIntros { x1 }; iIntro { x2 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) "}" :=
  iIntros { x1 x2 }; iIntro { x3 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) "}" :=
  iIntros { x1 x2 x3 }; iIntro { x4 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) "}" :=
  iIntros { x1 x2 x3 x4 }; iIntro { x5 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) "}" :=
  iIntros { x1 x2 x3 x4 x5 }; iIntro { x6 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) "}" :=
  iIntros { x1 x2 x3 x4 x5 x6 }; iIntro { x7 }.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) "}" :=
  iIntros { x1 x2 x3 x4 x5 x6 x7 }; iIntro { x8 }.

Tactic Notation "iIntros" "{" simple_intropattern(x1) "}" constr(p) :=
  iIntros { x1 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    "}" constr(p) :=
  iIntros { x1 x2 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) "}" constr(p) :=
  iIntros { x1 x2 x3 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) "}" constr(p) :=
  iIntros { x1 x2 x3 x4 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    "}" constr(p) :=
  iIntros { x1 x2 x3 x4 x5 }; iIntros p.
Tactic Notation "iIntros" "{"simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) "}" constr(p) :=
  iIntros { x1 x2 x3 x4 x5 x6 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) "}" constr(p) :=
  iIntros { x1 x2 x3 x4 x5 x6 x7 }; iIntros p.
Tactic Notation "iIntros" "{" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    "}" constr(p) :=
  iIntros { x1 x2 x3 x4 x5 x6 x7 x8 }; iIntros p.

(** * Later *)
Tactic Notation "iNext":=
  eapply tac_next;
    [apply _
    |let P := match goal with |- upred_tactics.StripLaterL ?P _ => P end in
     apply _ || fail "iNext:" P "does not contain laters"|].

(* This is pretty ugly, but without Ltac support for manipulating lists of
idents I do not know how to do this better. *)
Ltac iLöbCore IH tac_before tac_after :=
  match goal with
  | |- of_envs ?Δ ⊢ _ =>
     let Hs := constr:(rev (env_dom_list (env_spatial Δ))) in
     iRevert ★; tac_before;
     eapply tac_löb with _ IH;
       [reflexivity
       |env_cbv; reflexivity || fail "iLöb:" IH "not fresh"|];
    tac_after;  iIntros Hs
  end.

Tactic Notation "iLöb" "as" constr (IH) := iLöbCore IH idtac idtac.
Tactic Notation "iLöb" "{" ident(x1) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 }) ltac:(iIntros { x1 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 }) ltac:(iIntros { x1 x2 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 }) ltac:(iIntros { x1 x2 x3 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) ident(x4) "}" "as"
    constr (IH):=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 x4 }) ltac:(iIntros { x1 x2 x3 x4 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 x4 x5 })
              ltac:(iIntros { x1 x2 x3 x4 x5 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 x4 x5 x6 })
              ltac:(iIntros { x1 x2 x3 x4 x5 x6 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 x4 x5 x6 x7 })
              ltac:(iIntros { x1 x2 x3 x4 x5 x6 x7 }).
Tactic Notation "iLöb" "{" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) "}" "as" constr (IH) :=
  iLöbCore IH ltac:(iRevert { x1 x2 x3 x4 x5 x6 x7 x8 })
              ltac:(iIntros { x1 x2 x3 x4 x5 x6 x7 x8 }).

(** * Assert *)
Tactic Notation "iAssert" constr(Q) "as" constr(pat) "with" constr(Hs) :=
  let H := iFresh in
  let Hs := spec_pat.parse_one Hs in
  lazymatch Hs with
  | SSplit ?lr ?Hs =>
     eapply tac_assert with _ _ _ lr Hs H Q; (* (js:=Hs) (j:=H) (P:=Q) *)
       [env_cbv; reflexivity || fail "iAssert:" Hs "not found"
       |env_cbv; reflexivity|
       |iDestructHyp H as pat]
  | SPersistent =>
     eapply tac_assert_persistent with _ H Q; (* (j:=H) (P:=Q) *)
       [apply _ || fail "iAssert:" Q "not persistent"
       |env_cbv; reflexivity|
       |iDestructHyp H as pat]
  | ?pat => fail "iAssert: invalid pattern" pat
  end.
Tactic Notation "iAssert" constr(Q) "as" constr(pat) :=
  iAssert Q as pat with "[]".

(** * Rewrite *)
Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Tactic Notation "iRewriteCore" constr(lr) constr(Heq) :=
  eapply (tac_rewrite _ Heq _ _ lr);
    [env_cbv; reflexivity || fail "iRewrite:" Heq "not found"
    |let P := match goal with |- ?P ⊢ _ => P end in
     reflexivity || fail "iRewrite:" Heq ":" P "not an equality"
    |iRewriteFindPred
    |intros ??? ->; reflexivity|lazy beta].
Tactic Notation "iRewrite" constr(Heq) := iRewriteCore false Heq.
Tactic Notation "iRewrite" "-" constr(Heq) := iRewriteCore true Heq.

Tactic Notation "iRewriteCore" constr(lr) constr(Heq) "in" constr(H) :=
  eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
    [env_cbv; reflexivity || fail "iRewrite:" Heq "not found"
    |env_cbv; reflexivity || fail "iRewrite:" H "not found"
    |let P := match goal with |- ?P ⊢ _ => P end in
     reflexivity || fail "iRewrite:" Heq ":" P "not an equality"
    |iRewriteFindPred
    |intros ??? ->; reflexivity
    |env_cbv; reflexivity|lazy beta].
Tactic Notation "iRewrite" constr(Heq) "in" constr(H) :=
  iRewriteCore false Heq in H.
Tactic Notation "iRewrite" "-" constr(Heq) "in" constr(H) :=
  iRewriteCore true Heq in H.

(* Make sure that by and done solve trivial things in proof mode *)
Hint Extern 0 (of_envs _ ⊢ _) => by apply tac_pure_intro.
Hint Extern 0 (of_envs _ ⊢ _) => iAssumption.
