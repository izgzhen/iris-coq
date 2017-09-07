From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Export environments classes.
From stdpp Require Import stringmap hlist.
Set Default Proof Using "Type".
Import bi.
Import env_notations.

Local Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.

Record envs (PROP : bi) :=
  Envs { env_persistent : env PROP; env_spatial : env PROP }.
Add Printing Constructor envs.
Arguments Envs {_} _ _.
Arguments env_persistent {_} _.
Arguments env_spatial {_} _.

Record envs_wf {PROP} (Δ : envs PROP) := {
  env_persistent_valid : env_wf (env_persistent Δ);
  env_spatial_valid : env_wf (env_spatial Δ);
  envs_disjoint i : env_persistent Δ !! i = None ∨ env_spatial Δ !! i = None
}.

Coercion of_envs {PROP} (Δ : envs PROP) : PROP :=
  (⌜envs_wf Δ⌝ ∧ ⬕ [∧] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
Instance: Params (@of_envs) 1.
Arguments of_envs : simpl never.

Record envs_Forall2 {PROP : bi} (R : relation PROP) (Δ1 Δ2 : envs PROP) := {
  env_persistent_Forall2 : env_Forall2 R (env_persistent Δ1) (env_persistent Δ2);
  env_spatial_Forall2 : env_Forall2 R (env_spatial Δ1) (env_spatial Δ2)
}.

Definition envs_dom {PROP} (Δ : envs PROP) : list string :=
  env_dom (env_persistent Δ) ++ env_dom (env_spatial Δ).

Definition envs_lookup {PROP} (i : string) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P)
  | None => P ← env_lookup i Γs; Some (false, P)
  end.

Definition envs_delete {PROP} (i : string) (p : bool) (Δ : envs PROP) : envs PROP :=
  let (Γp,Γs) := Δ in
  match p with
  | true => Envs (env_delete i Γp) Γs
  | false => Envs Γp (env_delete i Γs)
  end.

Definition envs_lookup_delete {PROP} (i : string)
    (Δ : envs PROP) : option (bool * PROP * envs PROP) :=
  let (Γp,Γs) := Δ in
  match env_lookup_delete i Γp with
  | Some (P,Γp') => Some (true, P, Envs Γp' Γs)
  | None => '(P,Γs') ← env_lookup_delete i Γs; Some (false, P, Envs Γp Γs')
  end.

Fixpoint envs_lookup_delete_list {PROP} (js : list string) (remove_persistent : bool)
    (Δ : envs PROP) : option (bool * list PROP * envs PROP) :=
  match js with
  | [] => Some (true, [], Δ)
  | j :: js =>
     '(p,P,Δ') ← envs_lookup_delete j Δ;
     let Δ' := if p then (if remove_persistent then Δ' else Δ) else Δ' in
     '(q,Hs,Δ'') ← envs_lookup_delete_list js remove_persistent Δ';
     Some (p && q, P :: Hs, Δ'')
  end.

Definition envs_snoc {PROP} (Δ : envs PROP)
    (p : bool) (j : string) (P : PROP) : envs PROP :=
  let (Γp,Γs) := Δ in
  if p then Envs (Esnoc Γp j P) Γs else Envs Γp (Esnoc Γs j P).

Definition envs_app {PROP : bi} (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_simple_replace {PROP : bi} (i : string) (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_replace {PROP : bi} (i : string) (p q : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  if eqb p q then envs_simple_replace i p Γ Δ
  else envs_app q Γ (envs_delete i p Δ).

Definition env_spatial_is_nil {PROP} (Δ : envs PROP) : bool :=
  if env_spatial Δ is Enil then true else false.

Definition envs_clear_spatial {PROP} (Δ : envs PROP) : envs PROP :=
  Envs (env_persistent Δ) Enil.

Definition envs_clear_persistent {PROP} (Δ : envs PROP) : envs PROP :=
  Envs Enil (env_spatial Δ).

Fixpoint envs_split_go {PROP}
    (js : list string) (Δ1 Δ2 : envs PROP) : option (envs PROP * envs PROP) :=
  match js with
  | [] => Some (Δ1, Δ2)
  | j :: js =>
     '(p,P,Δ1') ← envs_lookup_delete j Δ1;
     if p then envs_split_go js Δ1 Δ2 else
     envs_split_go js Δ1' (envs_snoc Δ2 false j P)
  end.
(* if [lr = true] then [result = (remaining hyps, hyps named js)] and
   if [lr = false] then [result = (hyps named js, remaining hyps)] *)
Definition envs_split {PROP} (lr : bool)
    (js : list string) (Δ : envs PROP) : option (envs PROP * envs PROP) :=
  '(Δ1,Δ2) ← envs_split_go js Δ (envs_clear_spatial Δ);
  if lr then Some (Δ1,Δ2) else Some (Δ2,Δ1).

(* Coq versions of the tactics *)
Section bi_tactics.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Lemma of_envs_eq Δ :
  of_envs Δ = (⌜envs_wf Δ⌝ ∧ ⬕ [∧] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
Proof. done. Qed.

Lemma envs_lookup_delete_Some Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ')
  ↔ envs_lookup i Δ = Some (p,P) ∧ Δ' = envs_delete i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /envs_lookup_delete.
  destruct Δ as [Γp Γs]; rewrite /= !env_lookup_delete_correct.
  destruct (Γp !! i), (Γs !! i); naive_solver.
Qed.

Lemma envs_lookup_sound Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ ⬕?p P ∗ envs_delete i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /of_envs=>?. apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite pure_True ?left_id; last (destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γp) //= bare_persistently_and.
    by rewrite and_sep_bare_persistently -assoc.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite pure_True ?left_id; last (destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γs) //=. by rewrite !assoc -(comm _ P).
Qed.
Lemma envs_lookup_persistent_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → Δ ⊢ ⬕ P ∗ Δ.
Proof.
  intros. rewrite -persistently_and_bare_sep_l. apply and_intro; last done.
  rewrite envs_lookup_sound //; simpl.
  by rewrite -persistently_and_bare_sep_l and_elim_l.
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ ⬕?p P ∗ (⬕?p P -∗ Δ).
Proof.
  rewrite /envs_lookup /of_envs=>?. apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite pure_True // left_id.
    rewrite (env_lookup_perm Γp) //= bare_persistently_and and_sep_bare_persistently.
    cancel [⬕ P]%I. apply wand_intro_l. solve_sep_entails.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=. rewrite pure_True // left_id.
    cancel [P]. apply wand_intro_l. solve_sep_entails.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ ⬕?p P ∗ Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound. Qed.

Lemma envs_lookup_delete_list_sound Δ Δ' js rp p Ps :
  envs_lookup_delete_list js rp Δ = Some (p,Ps,Δ') →
  Δ ⊢ ⬕?p [∗] Ps ∗ Δ'.
Proof.
  revert Δ Δ' p Ps. induction js as [|j js IH]=> Δ Δ'' p Ps ?; simplify_eq/=.
  { by rewrite bare_persistently_emp left_id. }
  destruct (envs_lookup_delete j Δ) as [[[q1 P] Δ']|] eqn:Hj; simplify_eq/=.
  apply envs_lookup_delete_Some in Hj as [Hj ->].
  destruct (envs_lookup_delete_list js rp _) as [[[q2 Ps'] ?]|] eqn:?; simplify_eq/=.
  rewrite -bare_persistently_if_sep_2 -assoc. destruct q1; simpl.
  - destruct rp.
    + rewrite envs_lookup_sound //; simpl.
      by rewrite IH // (bare_persistently_bare_persistently_if q2).
    + rewrite envs_lookup_persistent_sound //.
      by rewrite IH // (bare_persistently_bare_persistently_if q2).
  - rewrite envs_lookup_sound // IH //; simpl. by rewrite bare_persistently_if_elim.
Qed.

Lemma envs_lookup_snoc Δ i p P :
  envs_lookup i Δ = None → envs_lookup i (envs_snoc Δ p i P) = Some (p, P).
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p, (Γp !! i); simplify_eq; by rewrite env_lookup_snoc.
Qed.
Lemma envs_lookup_snoc_ne Δ i j p P :
  i ≠ j → envs_lookup i (envs_snoc Δ p j P) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p; simplify_eq; by rewrite env_lookup_snoc_ne.
Qed.

Lemma envs_snoc_sound Δ p i P :
  envs_lookup i Δ = None → Δ ⊢ ⬕?p P -∗ envs_snoc Δ p i P.
Proof.
  rewrite /envs_lookup /envs_snoc /of_envs=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?, (Γs !! i) eqn:?; simplify_eq/=.
  apply wand_intro_l; destruct p; simpl.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (strings.string_beq_reflect j i); naive_solver.
    + by rewrite bare_persistently_and and_sep_bare_persistently assoc.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (strings.string_beq_reflect j i); naive_solver.
    + solve_sep_entails.
Qed.

Lemma envs_app_sound Δ Δ' p Γ :
  envs_app p Γ Δ = Some Δ' → Δ ⊢ (if p then ⬕ [∧] Γ else [∗] Γ) -∗ Δ'.
Proof.
  rewrite /of_envs /envs_app=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_opL_app bare_persistently_and and_sep_bare_persistently.
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_app_singleton_sound Δ Δ' p j Q :
  envs_app p (Esnoc Enil j Q) Δ = Some Δ' → Δ ⊢ ⬕?p Q -∗ Δ'.
Proof. move=> /envs_app_sound. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ (if p then ⬕ [∧] Γ else [∗] Γ) -∗ Δ'.
Proof.
  rewrite /envs_simple_replace /envs_delete /of_envs=> ?.
  apply pure_elim_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_opL_app bare_persistently_and and_sep_bare_persistently.
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_singleton_sound' Δ Δ' i p j Q :
  envs_simple_replace i p (Esnoc Enil j Q) Δ = Some Δ' →
  envs_delete i p Δ ⊢ ⬕?p Q -∗ Δ'.
Proof. move=> /envs_simple_replace_sound'. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  Δ ⊢ ⬕?p P ∗ ((if p then ⬕ [∧] Γ else [∗] Γ) -∗ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_simple_replace_singleton_sound Δ Δ' i p P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j Q) Δ = Some Δ' →
  Δ ⊢ ⬕?p P ∗ (⬕?p Q -∗ Δ').
Proof.
  intros. by rewrite envs_lookup_sound// envs_simple_replace_singleton_sound'//.
Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ (if q then ⬕ [∧] Γ else [∗] Γ) -∗ Δ'.
Proof.
  rewrite /envs_replace; destruct (eqb _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_singleton_sound' Δ Δ' i p q j Q :
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  envs_delete i p Δ ⊢ ⬕?q Q -∗ Δ'.
Proof. move=> /envs_replace_sound'. destruct q; by rewrite /= ?right_id. Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  Δ ⊢ ⬕?p P ∗ ((if q then ⬕ [∧] Γ else [∗] Γ) -∗ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_replace_singleton_sound Δ Δ' i p q P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  Δ ⊢ ⬕?p P ∗ (⬕?q Q -∗ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_singleton_sound'//. Qed.

Lemma envs_lookup_envs_clear_spatial Δ j :
  envs_lookup j (envs_clear_spatial Δ)
  = '(p,P) ← envs_lookup j Δ; if p then Some (p,P) else None.
Proof.
  rewrite /envs_lookup /envs_clear_spatial.
  destruct Δ as [Γp Γs]; simpl; destruct (Γp !! j) eqn:?; simplify_eq/=; auto.
  by destruct (Γs !! j).
Qed.

Lemma envs_clear_spatial_sound Δ :
  Δ ⊢ envs_clear_spatial Δ ∗ [∗] env_spatial Δ.
Proof.
  rewrite /of_envs /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
  rewrite right_id -persistent_and_sep_assoc. apply and_intro; [|done].
  apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_spatial_is_nil_bare_persistently Δ :
  env_spatial_is_nil Δ = true → Δ ⊢ ⬕ Δ.
Proof.
  intros. unfold of_envs; destruct Δ as [? []]; simplify_eq/=.
  rewrite !right_id {1}bare_and_r persistently_and.
  by rewrite persistently_bare persistently_idemp persistently_pure.
Qed.

Lemma envs_lookup_envs_delete Δ i p P :
  envs_wf Δ →
  envs_lookup i Δ = Some (p,P) → envs_lookup i (envs_delete i p Δ) = None.
Proof.
  rewrite /envs_lookup /envs_delete=> -[?? Hdisj] Hlookup.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - rewrite env_lookup_env_delete //. revert Hlookup.
    destruct (Hdisj i) as [->| ->]; [|done]. by destruct (Γs !! _).
  - rewrite env_lookup_env_delete //. by destruct (Γp !! _).
Qed.
Lemma envs_lookup_envs_delete_ne Δ i j p :
  i ≠ j → envs_lookup i (envs_delete j p Δ) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_delete=> ?. destruct Δ as [Γp Γs],p; simplify_eq/=.
  - by rewrite env_lookup_env_delete_ne.
  - destruct (Γp !! i); simplify_eq/=; by rewrite ?env_lookup_env_delete_ne.
Qed.

Lemma envs_split_go_sound js Δ1 Δ2 Δ1' Δ2' :
  (∀ j P, envs_lookup j Δ1 = Some (false, P) → envs_lookup j Δ2 = None) →
  envs_split_go js Δ1 Δ2 = Some (Δ1',Δ2') →
  Δ1 ∗ Δ2 ⊢ Δ1' ∗ Δ2'.
Proof.
  revert Δ1 Δ2 Δ1' Δ2'.
  induction js as [|j js IH]=> Δ1 Δ2 Δ1' Δ2' Hlookup HΔ; simplify_eq/=; [done|].
  apply pure_elim with (envs_wf Δ1)=> [|Hwf].
  { by rewrite /of_envs !and_elim_l sep_elim_l. }
  destruct (envs_lookup_delete j Δ1)
    as [[[[] P] Δ1'']|] eqn:Hdel; simplify_eq; auto.
  apply envs_lookup_delete_Some in Hdel as [??]; subst.
  rewrite envs_lookup_sound //; rewrite /= (comm _ P) -assoc.
  rewrite -(IH _ _ _ _ _ HΔ); last first.
  { intros j' P'; destruct (decide (j = j')) as [->|].
    - by rewrite (envs_lookup_envs_delete _ _ _ P).
    - rewrite envs_lookup_envs_delete_ne // envs_lookup_snoc_ne //. eauto. }
  rewrite (envs_snoc_sound Δ2 false j P) /= ?wand_elim_r; eauto.
Qed.
Lemma envs_split_sound Δ lr js Δ1 Δ2 :
  envs_split lr js Δ = Some (Δ1,Δ2) → Δ ⊢ Δ1 ∗ Δ2.
Proof.
  rewrite /envs_split=> ?. rewrite -(idemp bi_and Δ).
  rewrite {2}envs_clear_spatial_sound.
  rewrite (env_spatial_is_nil_bare_persistently (envs_clear_spatial _)) //.
  rewrite -persistently_and_bare_sep_l.
  rewrite (and_elim_l (□ _)%I) persistently_and_bare_sep_r bare_persistently_elim.
  destruct (envs_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done].
  apply envs_split_go_sound in HΔ as ->; last first.
  { intros j P. by rewrite envs_lookup_envs_clear_spatial=> ->. }
  destruct lr; simplify_eq; solve_sep_entails.
Qed.

Global Instance envs_Forall2_refl (R : relation PROP) :
  Reflexive R → Reflexive (envs_Forall2 R).
Proof. by constructor. Qed.
Global Instance envs_Forall2_sym (R : relation PROP) :
  Symmetric R → Symmetric (envs_Forall2 R).
Proof. intros ??? [??]; by constructor. Qed.
Global Instance envs_Forall2_trans (R : relation PROP) :
  Transitive R → Transitive (envs_Forall2 R).
Proof. intros ??? [??] [??] [??]; constructor; etrans; eauto. Qed.
Global Instance envs_Forall2_antisymm (R R' : relation PROP) :
  AntiSymm R R' → AntiSymm (envs_Forall2 R) (envs_Forall2 R').
Proof. intros ??? [??] [??]; constructor; by eapply (anti_symm _). Qed.
Lemma envs_Forall2_impl (R R' : relation PROP) Δ1 Δ2 :
  envs_Forall2 R Δ1 Δ2 → (∀ P Q, R P Q → R' P Q) → envs_Forall2 R' Δ1 Δ2.
Proof. intros [??] ?; constructor; eauto using env_Forall2_impl. Qed.

Global Instance of_envs_mono : Proper (envs_Forall2 (⊢) ==> (⊢)) (@of_envs PROP).
Proof.
  intros [Γp1 Γs1] [Γp2 Γs2] [Hp Hs]; apply and_mono; simpl in *.
  - apply pure_mono=> -[???]. constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - by repeat f_equiv.
Qed.
Global Instance of_envs_proper :
  Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢)) (@of_envs PROP).
Proof.
  intros Δ1 Δ2 HΔ; apply (anti_symm (⊢)); apply of_envs_mono;
    eapply (envs_Forall2_impl (⊣⊢)); [| |symmetry|]; eauto using equiv_entails.
Qed.
Global Instance Envs_mono (R : relation PROP) :
  Proper (env_Forall2 R ==> env_Forall2 R ==> envs_Forall2 R) (@Envs PROP).
Proof. by constructor. Qed.

(** * Adequacy *)
Lemma tac_adequate P : (Envs Enil Enil ⊢ P) → P.
Proof.
  intros <-. rewrite /of_envs /= persistently_True_emp bare_persistently_emp left_id.
  apply and_intro=> //. apply pure_intro; repeat constructor.
Qed.

(** * Basic rules *)
Class AffineEnv (Γ : env PROP) := affine_env : Forall Affine Γ.
Global Instance affine_env_nil : AffineEnv Enil.
Proof. constructor. Qed.
Global Instance affine_env_snoc Γ i P :
  Affine P → AffineEnv Γ → AffineEnv (Esnoc Γ i P).
Proof. by constructor. Qed.

Instance affine_env_spatial Δ :
  TCOr (AffineBI PROP) (AffineEnv (env_spatial Δ)) → Affine ([∗] env_spatial Δ).
Proof. destruct 1 as [?|H]. apply _. induction H; simpl; apply _. Qed.

Lemma tac_emp_intro Δ :
  (* Establishing [AffineEnv (env_spatial Δ)] is rather expensive (linear in the
  size of the context), so first check whether the whole BI is affine (which
  takes constant time). *)
  TCOr (AffineBI PROP) (AffineEnv (env_spatial Δ)) →
  Δ ⊢ emp.
Proof. intros. by rewrite (affine Δ). Qed.

Lemma tac_assumption Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  FromAssumption p P Q →
  (if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  Δ ⊢ Q.
Proof.
  intros ?? H. rewrite envs_lookup_delete_sound //.
  destruct (env_spatial_is_nil Δ') eqn:?.
  - by rewrite (env_spatial_is_nil_bare_persistently Δ') // sep_elim_l.
  - rewrite from_assumption. destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_rename Δ Δ' i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_singleton_sound //.
  by rewrite wand_elim_r.
Qed.

Lemma tac_clear Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  (Δ' ⊢ Q) →
  Δ ⊢ Q.
Proof.
  intros ? Hp HQ. rewrite envs_lookup_delete_sound //.
  destruct p; by rewrite /= HQ sep_elim_r.
Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : (Δ ⊢ False) → Δ ⊢ Q.
Proof. by rewrite -(False_elim Q). Qed.

Lemma tac_false_destruct Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  P = False%I →
  Δ ⊢ Q.
Proof.
  intros ? ->. rewrite envs_lookup_sound //; simpl.
  by rewrite bare_persistently_if_elim sep_elim_l False_elim.
Qed.

(** * Pure *)
Lemma tac_pure_intro Δ Q (φ : Prop) : FromPure Q φ → φ → Δ ⊢ Q.
Proof. intros ??. rewrite -(from_pure Q). by apply pure_intro. Qed.

Lemma tac_pure Δ Δ' i p P φ Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  IntoPure P φ →
  (if p then TCTrue else Affine P) →
  (φ → Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? HQ. rewrite envs_lookup_delete_sound //; simpl. destruct p; simpl.
  - rewrite (into_pure P) -persistently_and_bare_sep_l persistently_pure.
    by apply pure_elim_l.
  - rewrite -(affine_bare P) (into_pure P) -persistent_and_bare_sep_l.
    by apply pure_elim_l.
Qed.

Lemma tac_pure_revert Δ φ Q : (Δ ⊢ ⌜φ⌝ → Q) → (φ → Δ ⊢ Q).
Proof. intros HΔ ?. by rewrite HΔ pure_True // left_id. Qed.

(** * Persistently *)
Lemma tac_persistently_intro Δ a p Q Q' :
  FromPersistent a p Q' Q →
  (if a then TCOr (AffineBI PROP) (AffineEnv (env_spatial Δ)) else TCTrue) →
  ((if p then envs_clear_spatial Δ else Δ) ⊢ Q) → Δ ⊢ Q'.
Proof.
  intros ? Haffine HQ. rewrite -(from_persistent a p Q') -HQ. destruct p=> /=.
  - rewrite envs_clear_spatial_sound.
    rewrite {1}(env_spatial_is_nil_bare_persistently (envs_clear_spatial Δ)) //.
    destruct a=> /=. by rewrite sep_elim_l. by rewrite bare_elim sep_elim_l.
  - destruct a=> //=. apply and_intro; auto using tac_emp_intro.
Qed.

Lemma tac_persistent Δ Δ' i p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPersistent p P P' →
  (if p then TCTrue else Affine P) →
  envs_replace i p true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? <-. rewrite envs_replace_singleton_sound //; simpl.
  apply wand_elim_r', wand_mono=> //. destruct p; simpl.
  - by rewrite -(into_persistent _ P).
  - by rewrite -(into_persistent _ P) /= affine_bare.
Qed.

(** * Implication and wand *)
Lemma envs_app_singleton_sound_foo Δ Δ' p j Q :
  envs_app p (Esnoc Enil j Q) Δ = Some Δ' → Δ ∗ ⬕?p Q ⊢ Δ'.
Proof. intros. apply wand_elim_l'. eapply envs_app_singleton_sound. eauto. Qed.

Lemma tac_impl_intro Δ Δ' i P P' Q :
  (if env_spatial_is_nil Δ then TCTrue else Persistent P) →
  envs_app false (Esnoc Enil i P') Δ = Some Δ' →
  FromBare P' P →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ??? <-. destruct (env_spatial_is_nil Δ) eqn:?.
  - rewrite (env_spatial_is_nil_bare_persistently Δ) //; simpl. apply impl_intro_l.
    rewrite envs_app_singleton_sound //; simpl.
    rewrite -(from_bare P') -bare_and_lr.
    by rewrite persistently_and_bare_sep_r bare_persistently_elim wand_elim_r.
  - apply impl_intro_l. rewrite envs_app_singleton_sound //; simpl.
    by rewrite -(from_bare P') persistent_and_bare_sep_l_1 wand_elim_r.
Qed.
Lemma tac_impl_intro_persistent Δ Δ' i P P' Q :
  IntoPersistent false P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ?? <-. rewrite envs_app_singleton_sound //; simpl. apply impl_intro_l.
  rewrite (_ : P = □?false P)%I // (into_persistent false P).
  by rewrite persistently_and_bare_sep_l wand_elim_r.
Qed.
Lemma tac_pure_impl_intro Δ (φ ψ : Prop) :
  (φ → Δ ⊢ ⌜ψ⌝) → Δ ⊢ ⌜φ → ψ⌝.
Proof. intros. rewrite pure_impl. by apply impl_intro_l, pure_elim_l. Qed.
Lemma tac_impl_intro_pure Δ P φ Q : IntoPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros. apply impl_intro_l. rewrite (into_pure P). by apply pure_elim_l.
Qed.

Lemma tac_impl_intro_drop Δ P Q : (Δ ⊢ Q) → Δ ⊢ P → Q.
Proof. intros. apply impl_intro_l. by rewrite and_elim_r. Qed.

Lemma tac_wand_intro Δ Δ' i P Q :
  envs_app false (Esnoc Enil i P) Δ = Some Δ' → (Δ' ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros ? HQ. rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.
Lemma tac_wand_intro_persistent Δ Δ' i P P' Q :
  IntoPersistent false P P' →
  Affine P →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros ??? <-. rewrite envs_app_singleton_sound //; simpl.
  apply wand_mono=>//. by rewrite -(into_persistent _ P) /= affine_bare.
Qed.
Lemma tac_wand_intro_pure Δ P φ Q :
  IntoPure P φ →
  Affine P →
  (φ → Δ ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros. apply wand_intro_l. rewrite -(affine_bare P) (into_pure P).
  rewrite -persistent_and_bare_sep_l. by apply pure_elim_l.
Qed.
Lemma tac_wand_intro_drop Δ P Q :
  TCOr (Affine P) (Absorbing Q) →
  (Δ ⊢ Q) →
  Δ ⊢ P -∗ Q.
Proof. intros HPQ ->. apply wand_intro_l. by rewrite sep_elim_r. Qed.

(* This is pretty much [tac_specialize_assert] with [js:=[j]] and [tac_exact],
but it is doing some work to keep the order of hypotheses preserved. *)
Lemma tac_specialize Δ Δ' Δ'' i p j q P1 P2 R Q :
  envs_lookup_delete i Δ = Some (p, P1, Δ') →
  envs_lookup j (if p then Δ else Δ') = Some (q, R) →
  IntoWand q p R P1 P2 →
  match p with
  | true  => envs_simple_replace j q (Esnoc Enil j P2) Δ
  | false => envs_replace j q false (Esnoc Enil j P2) Δ'
             (* remove [i] and make [j] spatial *)
  end = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? <-. destruct p.
  - rewrite envs_lookup_persistent_sound //.
    rewrite envs_simple_replace_singleton_sound //; simpl.
    rewrite -bare_persistently_if_idemp -bare_persistently_idemp into_wand /=.
    rewrite assoc (bare_persistently_bare_persistently_if q).
    by rewrite bare_persistently_if_sep_2 wand_elim_r wand_elim_r.
  - rewrite envs_lookup_sound //; simpl.
    rewrite envs_lookup_sound // (envs_replace_singleton_sound' _ Δ'') //; simpl.
    by rewrite into_wand /= assoc wand_elim_r wand_elim_r.
Qed.

Lemma tac_specialize_assert Δ Δ' Δ1 Δ2' j q lr js R P1 P2 P1' Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q false R P1 P2 →
  ElimModal P1' P1 Q Q →
  ('(Δ1,Δ2) ← envs_split lr js Δ';
    Δ2' ← envs_app false (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2')) = Some (Δ1,Δ2') → (* does not preserve position of [j] *)
  (Δ1 ⊢ P1') → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 HQ.
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl.
  rewrite HP1 into_wand /= -(elim_modal P1' P1 Q Q). cancel [P1'].
  apply wand_intro_l. by rewrite assoc !wand_elim_r.
Qed.

Lemma tac_unlock P Q : (P ⊢ Q) → P ⊢ locked Q.
Proof. by unlock. Qed.

Lemma tac_specialize_frame Δ Δ' j q R P1 P2 P1' Q Q' :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q false R P1 P2 →
  ElimModal P1' P1 Q Q →
  (Δ' ⊢ P1' ∗ locked Q') →
  Q' = (P2 -∗ Q)%I →
  Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ?? HPQ ->.
  rewrite envs_lookup_sound //. rewrite HPQ -lock.
  rewrite into_wand -{2}(elim_modal P1' P1 Q Q). cancel [P1'].
  apply wand_intro_l. by rewrite assoc !wand_elim_r.
Qed.

Lemma tac_specialize_assert_pure Δ Δ' j q R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q true R P1 P2 →
  FromPure P1 φ →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ' →
  φ → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_singleton_sound //; simpl.
  rewrite -bare_persistently_if_idemp into_wand /= -(from_pure P1).
  rewrite pure_True // persistently_pure bare_True_emp bare_emp.
  by rewrite emp_wand wand_elim_r.
Qed.

Lemma tac_specialize_assert_persistent Δ Δ' Δ'' j q P1 P1' P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q true R P1 P2 →
  Persistent P1 →
  IntoSink P1' P1 →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ'' →
  (Δ' ⊢ P1') → (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ???? HP1 <-.
  rewrite envs_lookup_sound //.
  rewrite -(idemp bi_and (envs_delete _ _ _)).
  rewrite {2}envs_simple_replace_singleton_sound' //; simpl.
  rewrite {1}HP1 (into_sink P1') (persistent_persistently_2 P1) sink_persistently.
  rewrite persistently_and_bare_sep_l assoc.
  rewrite -bare_persistently_if_idemp -bare_persistently_idemp.
  rewrite (bare_persistently_bare_persistently_if q) bare_persistently_if_sep_2.
  by rewrite into_wand wand_elim_l wand_elim_r.
Qed.

Lemma tac_specialize_persistent_helper Δ Δ'' j q P R R' Q :
  envs_lookup j Δ = Some (q,P) →
  (Δ ⊢ ▲ R) →
  IntoPersistent false R R' →
  (if q then TCTrue else AffineBI PROP) →
  envs_replace j q true (Esnoc Enil j R') Δ = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ? HR ? Hpos ? <-. rewrite -(idemp bi_and Δ) {1}HR.
  rewrite envs_replace_singleton_sound //; destruct q; simpl.
  - rewrite (_ : R = □?false R)%I // (into_persistent _ R) sink_persistently.
    by rewrite sep_elim_r persistently_and_bare_sep_l wand_elim_r.
  - rewrite (absorbing_sink R) (_ : R = □?false R)%I // (into_persistent _ R).
    by rewrite sep_elim_r persistently_and_bare_sep_l wand_elim_r.
Qed.

Lemma tac_revert Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  (Δ' ⊢ (if p then ⬕ P else P) -∗ Q) → Δ ⊢ Q.
Proof.
  intros ? HQ. rewrite envs_lookup_delete_sound //; simpl.
  rewrite HQ. destruct p; simpl; auto using wand_elim_r.
Qed.

Class IntoIH {PROP : bi} (φ : Prop) (Δ : envs PROP) (Q : PROP) :=
  into_ih : φ → Δ ⊢ Q.
Global Instance into_ih_entails Δ Q : IntoIH (of_envs Δ ⊢ Q) Δ Q.
Proof. by rewrite /IntoIH. Qed.
Global Instance into_ih_forall {A} (φ : A → Prop) Δ Φ :
  (∀ x, IntoIH (φ x) Δ (Φ x)) → IntoIH (∀ x, φ x) Δ (∀ x, Φ x)%I | 2.
Proof. rewrite /IntoIH=> HΔ ?. apply forall_intro=> x. by rewrite (HΔ x). Qed.
Global Instance into_ih_impl (φ ψ : Prop) Δ Q :
  IntoIH φ Δ Q → IntoIH (ψ → φ) Δ (⌜ψ⌝ → Q)%I | 1.
Proof. rewrite /IntoIH=> HΔ ?. apply impl_intro_l, pure_elim_l. auto. Qed.

Lemma tac_revert_ih Δ P Q {φ : Prop} (Hφ : φ) :
  IntoIH φ Δ P →
  env_spatial_is_nil Δ = true →
  (of_envs Δ ⊢ □ P → Q) →
  (of_envs Δ ⊢ Q).
Proof.
  rewrite /IntoIH. intros HP ? HPQ.
  rewrite (env_spatial_is_nil_bare_persistently Δ) //.
  rewrite -(idemp bi_and (⬕ Δ)%I) {1}HP // HPQ.
  by rewrite -{1}persistently_idemp !bare_persistently_elim impl_elim_r.
Qed.

Lemma tac_assert Δ Δ1 Δ2 Δ2' lr js j P P' Q :
  ElimModal P' P Q Q →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ2 = Some Δ2' →
  (Δ1 ⊢ P') → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? HP HQ. rewrite envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl. by rewrite HP HQ.
Qed.

Lemma tac_assert_persistent Δ Δ1 Δ2 Δ' lr js j P P' Q :
  envs_split lr js Δ = Some (Δ1,Δ2) →
  Persistent P →
  FromBare P' P →
  envs_app false (Esnoc Enil j P') Δ = Some Δ' →
  (Δ1 ⊢ P) → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? HP <-. rewrite -(idemp bi_and Δ) {1}envs_split_sound //.
  rewrite HP. rewrite (persistent_persistently_2 P) sep_elim_l.
  rewrite persistently_and_bare_sep_l -bare_idemp bare_persistently_elim from_bare.
  rewrite envs_app_singleton_sound //; simpl. by rewrite wand_elim_r.
Qed.

Lemma tac_assert_pure Δ Δ' j P P' φ Q :
  FromPure P φ →
  FromBare P' P →
  envs_app false (Esnoc Enil j P') Δ = Some Δ' →
  φ → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? <-. rewrite envs_app_singleton_sound //; simpl.
  rewrite -(from_bare P') -(from_pure P) pure_True //.
  by rewrite bare_True_emp bare_emp emp_wand.
Qed.

Lemma tac_pose_proof Δ Δ' j P Q :
  P →
  envs_app true (Esnoc Enil j P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros HP ? <-. rewrite envs_app_singleton_sound //; simpl.
  by rewrite -HP bare_persistently_emp emp_wand.
Qed.

Lemma tac_pose_proof_hyp Δ Δ' Δ'' i p j P Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  envs_app p (Esnoc Enil j P) (if p then Δ else Δ') = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_app_singleton_sound //; simpl.
    by rewrite wand_elim_r.
  - rewrite envs_lookup_sound // envs_app_singleton_sound //; simpl.
    by rewrite wand_elim_r.
Qed.

Lemma tac_apply Δ Δ' i p R P1 P2 :
  envs_lookup_delete i Δ = Some (p, R, Δ') →
  IntoWand p false R P1 P2 →
  (Δ' ⊢ P1) → Δ ⊢ P2.
Proof.
  intros ?? HP1. rewrite envs_lookup_delete_sound //.
  by rewrite into_wand /= HP1 wand_elim_l.
Qed.

(** * Rewriting *)
Lemma tac_rewrite Δ i p Pxy (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : ofeT} (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (Q ⊣⊢ Φ (if lr then y else x)) →
    NonExpansive Φ →
    (Δ ⊢ Φ (if lr then x else y)) → Δ ⊢ Q.
Proof.
  intros ? A x y ? HPxy -> ?; apply internal_eq_rewrite'; auto.
  rewrite {1}envs_lookup_sound //.
  rewrite HPxy bare_persistently_if_elim sep_elim_l.
  destruct lr; auto using internal_eq_sym.
Qed.

Lemma tac_rewrite_in Δ i p Pxy j q P (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P) →
  ∀ {A : ofeT} Δ' (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (P ⊣⊢ Φ (if lr then y else x)) →
    NonExpansive Φ →
    envs_simple_replace j q (Esnoc Enil j (Φ (if lr then x else y))) Δ = Some Δ' →
    (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? A Δ' x y Φ HPxy HP ?? <-.
  rewrite -(idemp bi_and Δ) {2}(envs_lookup_sound _ i) //.
  rewrite (envs_simple_replace_singleton_sound _ _ j) //; simpl.
  rewrite HP HPxy (bare_persistently_if_elim _ (_ ≡ _)%I) sep_elim_l.
  rewrite persistent_and_bare_sep_r -assoc. apply wand_elim_r'.
  rewrite -persistent_and_bare_sep_r. apply impl_elim_r'. destruct lr.
  - apply (internal_eq_rewrite x y (λ y, ⬕?q Φ y -∗ Δ')%I). solve_proper.
  - rewrite internal_eq_sym.
    eapply (internal_eq_rewrite y x (λ y, ⬕?q Φ y -∗ Δ')%I). solve_proper.
Qed.

(** * Conjunction splitting *)
Lemma tac_and_split Δ P Q1 Q2 :
  FromAnd P Q1 Q2 → (Δ ⊢ Q1) → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_and P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Lemma tac_sep_split Δ Δ1 Δ2 lr js P Q1 Q2 :
  FromSep P Q1 Q2 →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  (Δ1 ⊢ Q1) → (Δ2 ⊢ Q2) → Δ ⊢ P.
Proof. intros ?? HQ1 HQ2. rewrite envs_split_sound //. by rewrite HQ1 HQ2. Qed.

(** * Combining *)
Class FromSeps {PROP : bi} (P : PROP) (Qs : list PROP) :=
  from_seps : [∗] Qs ⊢ P.
Arguments FromSeps {_} _%I _%I.
Arguments from_seps {_} _%I _%I {_}.

Global Instance from_seps_nil : @FromSeps PROP emp [].
Proof. by rewrite /FromSeps. Qed.
Global Instance from_seps_singleton P : FromSeps P [P] | 1.
Proof. by rewrite /FromSeps /= right_id. Qed.
Global Instance from_seps_cons P P' Q Qs :
  FromSeps P' Qs → FromSep P Q P' → FromSeps P (Q :: Qs) | 2.
Proof. by rewrite /FromSeps /FromSep /= => ->. Qed.

Lemma tac_combine Δ1 Δ2 Δ3 js p Ps j P Q :
  envs_lookup_delete_list js false Δ1 = Some (p, Ps, Δ2) →
  FromSeps P Ps →
  envs_app p (Esnoc Enil j P) Δ2 = Some Δ3 →
  (Δ3 ⊢ Q) → Δ1 ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_lookup_delete_list_sound //.
  rewrite from_seps. rewrite envs_app_singleton_sound //; simpl.
  by rewrite wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Lemma tac_and_destruct Δ Δ' i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd true P P1 P2 else IntoSep P P1 P2) →
  envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl. destruct p.
  - by rewrite (into_and _ P) /= right_id -(comm _ P1) wand_elim_r.
  - by rewrite (into_sep P) right_id -(comm _ P1) wand_elim_r.
Qed.

(* Using this tactic, one can destruct a (non-separating) conjunction in the
spatial context as long as one of the conjuncts is thrown away. It corresponds
to the principle of "external choice" in linear logic. *)
Lemma tac_and_destruct_choice Δ Δ' i p (lr : bool) j P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd p P P1 P2 : Type else
    TCOr (IntoAnd p P P1 P2) (TCAnd (IntoSep P P1 P2)
      (if lr then TCOr (Affine P2) (Absorbing Q)
       else TCOr (Affine P1) (Absorbing Q)))) →
  envs_simple_replace i p (Esnoc Enil j (if lr then P1 else P2)) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ? HP ? HQ. rewrite envs_simple_replace_singleton_sound //; simpl.
  destruct p.
  { rewrite (into_and _ P) HQ. destruct lr; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  destruct HP as [?|[??]].
  { rewrite (into_and _ P) HQ. destruct lr; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  rewrite (into_sep P) HQ. destruct lr; simpl.
  - by rewrite (comm _ P1) -assoc wand_elim_r sep_elim_r.
  - by rewrite -assoc wand_elim_r sep_elim_r.
Qed.

(** * Framing *)
Lemma tac_frame_pure Δ (φ : Prop) P Q :
  φ → Frame true ⌜φ⌝ P Q → (Δ ⊢ Q) → Δ ⊢ P.
Proof.
  intros ?? ->. rewrite -(frame ⌜φ⌝ P) /=.
  rewrite -persistently_and_bare_sep_l persistently_pure. auto using and_intro, pure_intro.
Qed.

Lemma tac_frame Δ Δ' i p R P Q :
  envs_lookup_delete i Δ = Some (p, R, Δ') →
  Frame p R P Q →
  ((if p then Δ else Δ') ⊢ Q) → Δ ⊢ P.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? HQ. destruct p.
  - by rewrite envs_lookup_persistent_sound // -(frame R P) HQ.
  - rewrite envs_lookup_sound //; simpl. by rewrite -(frame R P) HQ.
Qed.

(** * Disjunction *)
Lemma tac_or_l Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q1) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_l'. Qed.
Lemma tac_or_r Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_r'. Qed.

Lemma tac_or_destruct Δ Δ1 Δ2 i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j1 P1) Δ = Some Δ1 →
  envs_simple_replace i p (Esnoc Enil j2 P2) Δ = Some Δ2 →
  (Δ1 ⊢ Q) → (Δ2 ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? HP1 HP2. rewrite envs_lookup_sound //.
  rewrite (into_or P) bare_persistently_if_or sep_or_r; apply or_elim.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ1) //.
    by rewrite wand_elim_r.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ2) //.
    by rewrite wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → PROP) Q :
  FromForall Q Φ →
  (∀ a, Δ ⊢ Φ a) →
  Δ ⊢ Q.
Proof. rewrite /FromForall=> <-. apply forall_intro. Qed.

Lemma tac_forall_specialize {A} Δ Δ' i p P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoForall P Φ →
  (∃ x : A,
    envs_simple_replace i p (Esnoc Enil i (Φ x)) Δ = Some Δ' ∧
    (Δ' ⊢ Q)) →
  Δ ⊢ Q.
Proof.
  intros ?? (x&?&?). rewrite envs_simple_replace_singleton_sound //; simpl.
  by rewrite (into_forall P) (forall_elim x) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → PROP) :
  (Δ ⊢ ∀ a, Φ a) → ∀ a, Δ ⊢ Φ a.
Proof. intros HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Lemma tac_exist {A} Δ P (Φ : A → PROP) :
  FromExist P Φ → (∃ a, Δ ⊢ Φ a) → Δ ⊢ P.
Proof. intros ? [a ?]. rewrite -(from_exist P). eauto using exist_intro'. Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ →
  (∀ a, ∃ Δ',
    envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ = Some Δ' ∧ (Δ' ⊢ Q)) →
  Δ ⊢ Q.
Proof.
  intros ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) bare_persistently_if_exist sep_exist_r.
  apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
  rewrite envs_simple_replace_singleton_sound' //; simpl. by rewrite wand_elim_r.
Qed.

(** * Modalities *)
Lemma tac_modal_intro Δ P Q : FromModal P Q → (Δ ⊢ Q) → Δ ⊢ P.
Proof. rewrite /FromModal. by intros <- ->. Qed.

Lemma tac_modal_elim Δ Δ' i p P' P Q Q' :
  envs_lookup i Δ = Some (p, P) →
  ElimModal P P' Q Q' →
  envs_replace i p false (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q') → Δ ⊢ Q.
Proof.
  intros ??? HΔ. rewrite envs_replace_singleton_sound //; simpl.
  rewrite HΔ bare_persistently_if_elim. by apply elim_modal.
Qed.
End bi_tactics.

Section sbi_tactics.
Context {PROP : sbi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

(** * Later *)
Class IntoLaterNEnv (n : nat) (Γ1 Γ2 : env PROP) :=
  into_laterN_env : env_Forall2 (IntoLaterN n) Γ1 Γ2.
Class IntoLaterNEnvs (n : nat) (Δ1 Δ2 : envs PROP) := {
  into_later_persistent: IntoLaterNEnv n (env_persistent Δ1) (env_persistent Δ2);
  into_later_spatial: IntoLaterNEnv n (env_spatial Δ1) (env_spatial Δ2)
}.

Global Instance into_laterN_env_nil n : IntoLaterNEnv n Enil Enil.
Proof. constructor. Qed.
Global Instance into_laterN_env_snoc n Γ1 Γ2 i P Q :
  IntoLaterNEnv n Γ1 Γ2 → IntoLaterN n P Q →
  IntoLaterNEnv n (Esnoc Γ1 i P) (Esnoc Γ2 i Q).
Proof. by constructor. Qed.

Global Instance into_laterN_envs n Γp1 Γp2 Γs1 Γs2 :
  IntoLaterNEnv n Γp1 Γp2 → IntoLaterNEnv n Γs1 Γs2 →
  IntoLaterNEnvs n (Envs Γp1 Γs1) (Envs Γp2 Γs2).
Proof. by split. Qed.

Lemma into_laterN_env_sound n Δ1 Δ2 :
  IntoLaterNEnvs n Δ1 Δ2 → Δ1 ⊢ ▷^n (Δ2 : bi_car _).
Proof.
  intros [Hp Hs]; rewrite /of_envs /= !laterN_and !laterN_sep.
  rewrite -{1}laterN_intro -laterN_bare_persistently_2.
  apply and_mono, sep_mono.
  - apply pure_mono; destruct 1; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - apply bare_mono, persistently_mono.
    induction Hp; rewrite /= ?laterN_and. apply laterN_intro. by apply and_mono.
  - induction Hs; rewrite /= ?laterN_sep. apply laterN_intro. by apply sep_mono.
Qed.

Lemma tac_next Δ Δ' n Q Q' :
  FromLaterN n Q Q' → IntoLaterNEnvs n Δ Δ' → (Δ' ⊢ Q') → Δ ⊢ Q.
Proof. intros ?? HQ. by rewrite -(from_laterN n Q) into_laterN_env_sound HQ. Qed.

Lemma tac_löb Δ Δ' i Q :
  env_spatial_is_nil Δ = true →
  envs_app true (Esnoc Enil i (▷ Q)%I) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite (env_spatial_is_nil_bare_persistently Δ) //.
  rewrite -(persistently_and_emp_elim Q). apply and_intro; first apply: affine.
  rewrite -(löb (□ Q)%I) later_persistently. apply impl_intro_l.
  rewrite envs_app_singleton_sound //; simpl; rewrite HQ.
  rewrite persistently_and_bare_sep_l -{1}bare_persistently_idemp bare_persistently_sep_2.
  by rewrite wand_elim_r bare_elim.
Qed.
End sbi_tactics.
