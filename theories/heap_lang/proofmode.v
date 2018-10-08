From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export tactics lifting.
From iris.heap_lang Require Import notation.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{heapG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
Lemma tac_twp_expr_eval `{heapG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    eapply tac_twp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.

Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_pure `{heapG Σ} Δ Δ' s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.
Lemma tac_twp_pure `{heapG Σ} Δ s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP e2 @ s; E [{ Φ }]) →
  envs_entails Δ (WP e1 @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ?? ->. rewrite -total_lifting.twp_pure_step //.
Qed.

Lemma tac_wp_value `{heapG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
Lemma tac_twp_value `{heapG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed.

Ltac wp_value_head :=
  first [eapply tac_wp_value || eapply tac_twp_value]; reduction.pm_prettify.

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try fast_done                  (* The pure condition for PureExec *)
      |iSolveTC                       (* IntoLaters *)
      |wp_expr_simpl; try wp_value_head (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_twp_pure _ _ _ (fill K e'));
      [iSolveTC                       (* PureExec *)
      |try fast_done                  (* The pure condition for PureExec *)
      |wp_expr_simpl; try wp_value_head (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* The `;[]` makes sure that no side-condition magically spawns. *)
Ltac wp_pures := repeat (wp_pure _; []).

(* The handling of beta-reductions with wp_rec needs special care in
  order to allow it to unlock locked `RecV` values: We first put
  `AsRecV_recv_locked` in the current environment so that it can be
  used as an instance by the typeclass resolution system, then we
  perform the reduction, and finally we clear this new hypothesis.

  The reason is that we do not want impure wp_ tactics to unfold
  locked terms, while we want them to execute arbitrary pure steps. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv_locked);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{heapG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.
Lemma tac_twp_bind `{heapG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> -> ->. by apply: twp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wp_alloc Δ Δ' s E j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc v) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.
Lemma tac_twp_alloc Δ s E j K v Φ :
  (∀ l, ∃ Δ',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ = Some Δ' ∧
    envs_entails Δ' (WP fill K (Val $ LitV l) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (Alloc v) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> HΔ.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_alloc.
  rewrite left_id. apply forall_intro=> l.
  destruct (HΔ l) as (Δ'&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' s E i K l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_load Δ s E i K l q v Φ :
  envs_lookup i Δ = Some (false, l ↦{q} v)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ??.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_load.
  rewrite envs_lookup_split //; simpl.
  by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_store Δ Δ' s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Store (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first by eapply twp_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  vals_cas_compare_safe v v1 →
  (v = v1 → envs_entails Δ'' (WP fill K (Val $ LitV true) @ s; E {{ Φ }})) →
  (v ≠ v1 → envs_entails Δ' (WP fill K (Val $ LitV false) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (CAS (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???? Hsuc Hfail. destruct (decide (v = v1)) as [<-|Hne].
  - rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_suc.
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wp_cas_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.
Lemma tac_twp_cas Δ Δ' s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ = Some Δ' →
  vals_cas_compare_safe v v1 →
  (v = v1 → envs_entails Δ' (WP fill K (Val $ LitV true) @ s; E [{ Φ }])) →
  (v ≠ v1 → envs_entails Δ (WP fill K (Val $ LitV false) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (CAS (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ??? Hsuc Hfail. destruct (decide (v = v1)) as [<-|Hne].
  - rewrite -twp_bind. eapply wand_apply; first exact: twp_cas_suc.
    rewrite /= {1}envs_simple_replace_sound //; simpl.
    apply sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -twp_bind. eapply wand_apply.
    { eapply twp_cas_fail; eauto. }
    rewrite /= {1}envs_lookup_split //; simpl.
    apply sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wp_cas_fail Δ Δ' s E i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_cas_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ LitV false) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ?????.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cas_fail Δ s E i K l q v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_cas_compare_safe v v1 →
  envs_entails Δ (WP fill K (Val $ LitV false) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CAS (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first exact: twp_cas_fail.
  rewrite envs_lookup_split //=. by do 2 f_equiv.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  v = v1 → val_is_unboxed v →
  envs_entails Δ'' (WP fill K (Val $ LitV true) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??????; subst.
  rewrite -wp_bind. eapply wand_apply.
  { eapply wp_cas_suc; eauto. by left. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cas_suc Δ Δ' s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ = Some Δ' →
  v = v1 → val_is_unboxed v →
  envs_entails Δ' (WP fill K (Val $ LitV true) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CAS (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=>?????; subst.
  rewrite -twp_bind. eapply wand_apply.
  { eapply twp_cas_suc; eauto. by left. }
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_faa Δ Δ' Δ'' s E i K l z1 z2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV z1)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (z1 + z2))) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV z1) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first exact: (wp_faa _ _ _ z1 z2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_faa Δ Δ' s E i K l z1 z2 Φ :
  envs_lookup i Δ = Some (false, l ↦ LitV z1)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (z1 + z2))) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Val $ LitV z1) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -twp_bind. eapply wand_apply; first exact: (twp_faa _ _ _ z1 z2).
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_pures;
  iPoseProofCore lem as false true (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; try wp_expr_simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; iApplyHyp H; try wp_expr_simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "not fresh"
        |iDestructHyp Htmp as H; wp_expr_simpl; try wp_value_head] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [iSolveTC
    |finish ()]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ _ Htmp K))
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    finish ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [iSolveTC
    |solve_mapsto ()
    |wp_expr_simpl; try wp_value_head]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [solve_mapsto ()
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  let finish _ :=
    wp_expr_simpl; try first [wp_seq|wp_value_head] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |finish ()]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |finish ()]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas _ _ _ _ _ _ K))
      |fail 1 "wp_cas: cannot find 'CAS' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |try (fast_done || (left; fast_done) || (right; fast_done)) (* vals_cas_compare_safe *)
    |intros H1; wp_expr_simpl; try wp_value_head
    |intros H2; wp_expr_simpl; try wp_value_head]
  | |- envs_entails _ (twp ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cas _ _ _ _ _ K))
      |fail 1 "wp_cas: cannot find 'CAS' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |try (fast_done || (left; fast_done) || (right; fast_done)) (* vals_cas_compare_safe *)
    |intros H1; wp_expr_simpl; try wp_value_head
    |intros H2; wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_cas: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_fail _ _ _ _ _ K))
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [iSolveTC
    |solve_mapsto ()
    |try congruence
    |try (fast_done || (left; fast_done) || (right; fast_done)) (* vals_cas_compare_safe *)
    |simpl; try wp_value_head]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cas_fail _ _ _ _ K))
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [solve_mapsto ()
    |try congruence
    |try (fast_done || (left; fast_done) || (right; fast_done)) (* vals_cas_compare_safe *)
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cas_suc _ _ _ _ _ _ K))
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |try congruence
    |try fast_done (* vals_cas_compare_safe *)
    |simpl; try wp_value_head]
  | |- envs_entails _ (twp ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cas_suc _ _ _ _ _ K))
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |try congruence
    |try fast_done (* vals_cas_compare_safe *)
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.

Tactic Notation "wp_faa" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_faa _ _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'CAS' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |wp_expr_simpl; try wp_value_head]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_faa _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'CAS' in" e];
    [solve_mapsto ()
    |pm_reflexivity
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_faa: not a 'wp'"
  end.
