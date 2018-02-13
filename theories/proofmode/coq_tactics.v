From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Export base environments classes.
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

Definition of_envs {PROP} (Δ : envs PROP) : PROP :=
  (⌜envs_wf Δ⌝ ∧ □ [∧] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
Instance: Params (@of_envs) 1.
Arguments of_envs : simpl never.

(* We seal [envs_entails], so that it does not get unfolded by the
   proofmode's own tactics, such as [iIntros (?)]. *)
Definition envs_entails_aux : seal (λ PROP (Δ : envs PROP) (Q : PROP), (of_envs Δ ⊢ Q)).
Proof. by eexists. Qed.
Definition envs_entails := unseal envs_entails_aux.
Definition envs_entails_eq : envs_entails = _ := seal_eq envs_entails_aux.
Arguments envs_entails {PROP} Δ Q%I : rename.
Instance: Params (@envs_entails) 1.

Record envs_Forall2 {PROP : bi} (R : relation PROP) (Δ1 Δ2 : envs PROP) := {
  env_persistent_Forall2 : env_Forall2 R (env_persistent Δ1) (env_persistent Δ2);
  env_spatial_Forall2 : env_Forall2 R (env_spatial Δ1) (env_spatial Δ2)
}.

Definition envs_dom {PROP} (Δ : envs PROP) : list ident :=
  env_dom (env_persistent Δ) ++ env_dom (env_spatial Δ).

Definition envs_lookup {PROP} (i : ident) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P)
  | None => P ← env_lookup i Γs; Some (false, P)
  end.

Definition envs_delete {PROP} (i : ident) (p : bool) (Δ : envs PROP) : envs PROP :=
  let (Γp,Γs) := Δ in
  match p with
  | true => Envs (env_delete i Γp) Γs
  | false => Envs Γp (env_delete i Γs)
  end.

Definition envs_lookup_delete {PROP} (i : ident)
    (Δ : envs PROP) : option (bool * PROP * envs PROP) :=
  let (Γp,Γs) := Δ in
  match env_lookup_delete i Γp with
  | Some (P,Γp') => Some (true, P, Envs Γp' Γs)
  | None => ''(P,Γs') ← env_lookup_delete i Γs; Some (false, P, Envs Γp Γs')
  end.

Fixpoint envs_lookup_delete_list {PROP} (js : list ident) (remove_persistent : bool)
    (Δ : envs PROP) : option (bool * list PROP * envs PROP) :=
  match js with
  | [] => Some (true, [], Δ)
  | j :: js =>
     ''(p,P,Δ') ← envs_lookup_delete j Δ;
     let Δ' := if p : bool then (if remove_persistent then Δ' else Δ) else Δ' in
     ''(q,Hs,Δ'') ← envs_lookup_delete_list js remove_persistent Δ';
     Some (p && q, P :: Hs, Δ'')
  end.

Definition envs_snoc {PROP} (Δ : envs PROP)
    (p : bool) (j : ident) (P : PROP) : envs PROP :=
  let (Γp,Γs) := Δ in
  if p then Envs (Esnoc Γp j P) Γs else Envs Γp (Esnoc Γs j P).

Definition envs_app {PROP : bi} (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_simple_replace {PROP : bi} (i : ident) (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_replace {PROP : bi} (i : ident) (p q : bool)
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
    (js : list ident) (Δ1 Δ2 : envs PROP) : option (envs PROP * envs PROP) :=
  match js with
  | [] => Some (Δ1, Δ2)
  | j :: js =>
     ''(p,P,Δ1') ← envs_lookup_delete j Δ1;
     if p : bool then envs_split_go js Δ1 Δ2 else
     envs_split_go js Δ1' (envs_snoc Δ2 false j P)
  end.
(* if [d = Right] then [result = (remaining hyps, hyps named js)] and
   if [d = Left] then [result = (hyps named js, remaining hyps)] *)
Definition envs_split {PROP} (d : direction)
    (js : list ident) (Δ : envs PROP) : option (envs PROP * envs PROP) :=
  ''(Δ1,Δ2) ← envs_split_go js Δ (envs_clear_spatial Δ);
  if d is Right then Some (Δ1,Δ2) else Some (Δ2,Δ1).

(* Coq versions of the tactics *)
Section bi_tactics.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Lemma of_envs_eq Δ :
  of_envs Δ = (⌜envs_wf Δ⌝ ∧ □ [∧] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
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
  envs_lookup i Δ = Some (p,P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete i p Δ).
Proof.
  rewrite /envs_lookup /envs_delete /of_envs=>?. apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite pure_True ?left_id; last (destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γp) //= affinely_persistently_and.
    by rewrite and_sep_affinely_persistently -assoc.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite pure_True ?left_id; last (destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γs) //=. by rewrite !assoc -(comm _ P).
Qed.
Lemma envs_lookup_persistent_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → of_envs Δ ⊢ □ P ∗ of_envs Δ.
Proof.
  intros. rewrite -persistently_and_affinely_sep_l. apply and_intro; last done.
  rewrite envs_lookup_sound //; simpl.
  by rewrite -persistently_and_affinely_sep_l and_elim_l.
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) → of_envs Δ ⊢ □?p P ∗ (□?p P -∗ of_envs Δ).
Proof.
  rewrite /envs_lookup /of_envs=>?. apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite pure_True // left_id (env_lookup_perm Γp) //=
            affinely_persistently_and and_sep_affinely_persistently.
    cancel [□ P]%I. apply wand_intro_l. solve_sep_entails.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=. rewrite pure_True // left_id.
    cancel [P]. apply wand_intro_l. solve_sep_entails.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → of_envs Δ ⊢ □?p P ∗ of_envs Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound. Qed.

Lemma envs_lookup_delete_list_sound Δ Δ' js rp p Ps :
  envs_lookup_delete_list js rp Δ = Some (p, Ps,Δ') →
  of_envs Δ ⊢ □?p [∗] Ps ∗ of_envs Δ'.
Proof.
  revert Δ Δ' p Ps. induction js as [|j js IH]=> Δ Δ'' p Ps ?; simplify_eq/=.
  { by rewrite affinely_persistently_emp left_id. }
  destruct (envs_lookup_delete j Δ) as [[[q1 P] Δ']|] eqn:Hj; simplify_eq/=.
  apply envs_lookup_delete_Some in Hj as [Hj ->].
  destruct (envs_lookup_delete_list js rp _) as [[[q2 Ps'] ?]|] eqn:?; simplify_eq/=.
  rewrite -affinely_persistently_if_sep_2 -assoc. destruct q1; simpl.
  - destruct rp.
    + rewrite envs_lookup_sound //; simpl.
      by rewrite IH // (affinely_persistently_affinely_persistently_if q2).
    + rewrite envs_lookup_persistent_sound //.
      by rewrite IH // (affinely_persistently_affinely_persistently_if q2).
  - rewrite envs_lookup_sound // IH //; simpl. by rewrite affinely_persistently_if_elim.
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
  envs_lookup i Δ = None → of_envs Δ ⊢ □?p P -∗ of_envs (envs_snoc Δ p i P).
Proof.
  rewrite /envs_lookup /envs_snoc /of_envs=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?, (Γs !! i) eqn:?; simplify_eq/=.
  apply wand_intro_l; destruct p; simpl.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (ident_beq_reflect j i); naive_solver.
    + by rewrite affinely_persistently_and and_sep_affinely_persistently assoc.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (ident_beq_reflect j i); naive_solver.
    + solve_sep_entails.
Qed.

Lemma envs_app_sound Δ Δ' p Γ :
  envs_app p Γ Δ = Some Δ' →
  of_envs Δ ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
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
      rewrite big_opL_app affinely_persistently_and and_sep_affinely_persistently.
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
  envs_app p (Esnoc Enil j Q) Δ = Some Δ' → of_envs Δ ⊢ □?p Q -∗ of_envs Δ'.
Proof. move=> /envs_app_sound. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs (envs_delete i p Δ) ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
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
      rewrite big_opL_app affinely_persistently_and and_sep_affinely_persistently.
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
  of_envs (envs_delete i p Δ) ⊢ □?p Q -∗ of_envs Δ'.
Proof. move=> /envs_simple_replace_sound'. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ ((if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_simple_replace_singleton_sound Δ Δ' i p P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ (□?p Q -∗ of_envs Δ').
Proof.
  intros. by rewrite envs_lookup_sound// envs_simple_replace_singleton_sound'//.
Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' →
  of_envs (envs_delete i p Δ) ⊢ (if q then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite /envs_replace; destruct (eqb _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_singleton_sound' Δ Δ' i p q j Q :
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs (envs_delete i p Δ) ⊢ □?q Q -∗ of_envs Δ'.
Proof. move=> /envs_replace_sound'. destruct q; by rewrite /= ?right_id. Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ ((if q then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_replace_singleton_sound Δ Δ' i p q P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ (□?q Q -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_singleton_sound'//. Qed.

Lemma envs_lookup_envs_clear_spatial Δ j :
  envs_lookup j (envs_clear_spatial Δ)
  = ''(p,P) ← envs_lookup j Δ; if p : bool then Some (p,P) else None.
Proof.
  rewrite /envs_lookup /envs_clear_spatial.
  destruct Δ as [Γp Γs]; simpl; destruct (Γp !! j) eqn:?; simplify_eq/=; auto.
  by destruct (Γs !! j).
Qed.

Lemma envs_clear_spatial_sound Δ :
  of_envs Δ ⊢ of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ.
Proof.
  rewrite /of_envs /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
  rewrite right_id -persistent_and_sep_assoc. apply and_intro; [|done].
  apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_spatial_is_nil_affinely_persistently Δ :
  env_spatial_is_nil Δ = true → of_envs Δ ⊢ □ of_envs Δ.
Proof.
  intros. unfold of_envs; destruct Δ as [? []]; simplify_eq/=.
  rewrite !right_id {1}affinely_and_r persistently_and.
  by rewrite persistently_affinely persistently_idemp persistently_pure.
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
  of_envs Δ1 ∗ of_envs Δ2 ⊢ of_envs Δ1' ∗ of_envs Δ2'.
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
Lemma envs_split_sound Δ d js Δ1 Δ2 :
  envs_split d js Δ = Some (Δ1,Δ2) → of_envs Δ ⊢ of_envs Δ1 ∗ of_envs Δ2.
Proof.
  rewrite /envs_split=> ?. rewrite -(idemp bi_and (of_envs Δ)).
  rewrite {2}envs_clear_spatial_sound.
  rewrite (env_spatial_is_nil_affinely_persistently (envs_clear_spatial _)) //.
  rewrite -persistently_and_affinely_sep_l.
  rewrite (and_elim_l (bi_persistently _)%I)
          persistently_and_affinely_sep_r affinely_persistently_elim.
  destruct (envs_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done].
  apply envs_split_go_sound in HΔ as ->; last first.
  { intros j P. by rewrite envs_lookup_envs_clear_spatial=> ->. }
  destruct d; simplify_eq/=; solve_sep_entails.
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
Global Instance Envs_proper (R : relation PROP) :
  Proper (env_Forall2 R ==> env_Forall2 R ==> envs_Forall2 R) (@Envs PROP).
Proof. by constructor. Qed.

Global Instance envs_entails_proper :
  Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢) ==> iff) (@envs_entails PROP).
Proof. rewrite envs_entails_eq. solve_proper. Qed.
Global Instance envs_entails_flip_mono :
  Proper (envs_Forall2 (⊢) ==> flip (⊢) ==> flip impl) (@envs_entails PROP).
Proof. rewrite envs_entails_eq=> Δ1 Δ2 ? P1 P2 <- <-. by f_equiv. Qed.

(** * Adequacy *)
Lemma tac_adequate P : envs_entails (Envs Enil Enil) P → P.
Proof.
  rewrite envs_entails_eq /of_envs /= persistently_True_emp
          affinely_persistently_emp left_id=><-.
  apply and_intro=> //. apply pure_intro; repeat constructor.
Qed.

(** * Basic rules *)
Lemma tac_eval Δ Q Q' :
  Q = Q' →
  envs_entails Δ Q' → envs_entails Δ Q.
Proof. by intros ->. Qed.

Class AffineEnv (Γ : env PROP) := affine_env : Forall Affine Γ.
Global Instance affine_env_nil : AffineEnv Enil.
Proof. constructor. Qed.
Global Instance affine_env_snoc Γ i P :
  Affine P → AffineEnv Γ → AffineEnv (Esnoc Γ i P).
Proof. by constructor. Qed.

(* If the BI is affine, no need to walk on the whole environment. *)
Global Instance affine_env_bi `(BiAffine PROP) Γ : AffineEnv Γ | 0.
Proof. induction Γ; apply _. Qed.

Instance affine_env_spatial Δ :
  AffineEnv (env_spatial Δ) → Affine ([∗] env_spatial Δ).
Proof. intros H. induction H; simpl; apply _. Qed.

Lemma tac_emp_intro Δ : AffineEnv (env_spatial Δ) → of_envs Δ ⊢ emp.
Proof. intros. by rewrite (affine (of_envs Δ)). Qed.

Lemma tac_assumption Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  FromAssumption p P Q →
  (if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  of_envs Δ ⊢ Q.
Proof.
  intros ?? H. rewrite envs_lookup_delete_sound //.
  destruct (env_spatial_is_nil Δ') eqn:?.
  - by rewrite (env_spatial_is_nil_affinely_persistently Δ') // sep_elim_l.
  - rewrite from_assumption. destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_rename Δ Δ' i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j P) Δ = Some Δ' →
  envs_entails Δ' Q →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? <-. rewrite envs_simple_replace_singleton_sound //.
  by rewrite wand_elim_r.
Qed.

Lemma tac_clear Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  envs_entails Δ' Q →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? HQ. rewrite envs_lookup_delete_sound //.
  by destruct p; rewrite /= HQ sep_elim_r.
Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : envs_entails Δ False → envs_entails Δ Q.
Proof. by rewrite envs_entails_eq -(False_elim Q). Qed.

Lemma tac_false_destruct Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  P = False%I →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ??. subst. rewrite envs_lookup_sound //; simpl.
  by rewrite affinely_persistently_if_elim sep_elim_l False_elim.
Qed.

(** * Pure *)
Lemma tac_pure_intro Δ Q φ : FromPure false Q φ → φ → envs_entails Δ Q.
Proof. intros ??. rewrite envs_entails_eq -(from_pure _ Q). by apply pure_intro. Qed.

Lemma tac_pure Δ Δ' i p P φ Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  IntoPure P φ →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  (φ → envs_entails Δ' Q) → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? HPQ HQ.
  rewrite envs_lookup_delete_sound //; simpl. destruct p; simpl.
  - rewrite (into_pure P) -persistently_and_affinely_sep_l persistently_pure.
    by apply pure_elim_l.
  - destruct HPQ.
    + rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
      by apply pure_elim_l.
    + rewrite (into_pure P) (persistent_absorbingly_affinely ⌜ _ ⌝%I) absorbingly_sep_lr.
      rewrite -persistent_and_affinely_sep_l. apply pure_elim_l=> ?. by rewrite HQ.
Qed.

Lemma tac_pure_revert Δ φ Q : envs_entails Δ (⌜φ⌝ → Q) → (φ → envs_entails Δ Q).
Proof. rewrite envs_entails_eq. intros HΔ ?. by rewrite HΔ pure_True // left_id. Qed.

(** * Always modalities *)
Class FilterPersistentEnv
    (M : always_modality PROP) (C : PROP → Prop) (Γ1 Γ2 : env PROP) := {
  filter_persistent_env :
    (∀ P, C P → □ P ⊢ M (□ P)) →
    □ ([∧] Γ1) ⊢ M (□ ([∧] Γ2));
  filter_persistent_env_wf : env_wf Γ1 → env_wf Γ2;
  filter_persistent_env_dom i : Γ1 !! i = None → Γ2 !! i = None;
}.
Global Instance filter_persistent_env_nil M C : FilterPersistentEnv M C Enil Enil.
Proof.
  split=> // HC /=. rewrite !persistently_pure !affinely_True_emp.
  by rewrite affinely_emp -always_modality_emp.
Qed.
Global Instance filter_persistent_env_snoc M (C : PROP → Prop) Γ Γ' i P :
  C P →
  FilterPersistentEnv M C Γ Γ' →
  FilterPersistentEnv M C (Esnoc Γ i P) (Esnoc Γ' i P).
Proof.
  intros ? [HΓ Hwf Hdom]; split; simpl.
  - intros HC. rewrite affinely_persistently_and HC // HΓ //.
    by rewrite always_modality_and -affinely_persistently_and.
  - inversion 1; constructor; auto.
  - intros j. destruct (ident_beq _ _); naive_solver.
Qed.
Global Instance filter_persistent_env_snoc_not M (C : PROP → Prop) Γ Γ' i P :
  FilterPersistentEnv M C Γ Γ' →
  FilterPersistentEnv M C (Esnoc Γ i P) Γ' | 100.
Proof.
  intros [HΓ Hwf Hdom]; split; simpl.
  - intros HC. by rewrite and_elim_r HΓ.
  - inversion 1; auto.
  - intros j. destruct (ident_beq _ _); naive_solver.
Qed.

Class FilterSpatialEnv
    (M : always_modality PROP) (C : PROP → Prop) (Γ1 Γ2 : env PROP) := {
  filter_spatial_env :
    (∀ P, C P → P ⊢ M P) → (∀ P, Absorbing (M P)) →
    ([∗] Γ1) ⊢ M ([∗] Γ2);
  filter_spatial_env_wf : env_wf Γ1 → env_wf Γ2;
  filter_spatial_env_dom i : Γ1 !! i = None → Γ2 !! i = None;
}.
Global Instance filter_spatial_env_nil M C : FilterSpatialEnv M C Enil Enil.
Proof. split=> // HC /=. by rewrite -always_modality_emp. Qed.
Global Instance filter_spatial_env_snoc M (C : PROP → Prop) Γ Γ' i P :
  C P →
  FilterSpatialEnv M C Γ Γ' →
  FilterSpatialEnv M C (Esnoc Γ i P) (Esnoc Γ' i P).
Proof.
  intros ? [HΓ Hwf Hdom]; split; simpl.
  - intros HC ?. by rewrite {1}(HC P) // HΓ // always_modality_sep.
  - inversion 1; constructor; auto.
  - intros j. destruct (ident_beq _ _); naive_solver.
Qed.

Global Instance filter_spatial_env_snoc_not M (C : PROP → Prop) Γ Γ' i P :
  FilterSpatialEnv M C Γ Γ' →
  FilterSpatialEnv M C (Esnoc Γ i P) Γ' | 100.
Proof.
  intros [HΓ Hwf Hdom]; split; simpl.
  - intros HC ?. by rewrite HΓ // sep_elim_r.
  - inversion 1; auto.
  - intros j. destruct (ident_beq _ _); naive_solver.
Qed.

Ltac tac_always_cases :=
  simplify_eq/=;
  repeat match goal with
  | H : TCAnd _ _ |- _ => destruct H
  | H : TCEq ?x _ |- _ => inversion H; subst x; clear H
  | H : TCForall _ _ |- _ => apply TCForall_Forall in H
  | H : FilterPersistentEnv _ _ _ _ |- _ => destruct H
  | H : FilterSpatialEnv _ _ _ _ |- _ => destruct H
  end; simpl; auto using Enil_wf.

Lemma tac_always_intro Γp Γs Γp' Γs' M Q Q' :
  FromAlways M Q' Q →
  match always_modality_persistent_spec M with
  | AIEnvForall C => TCAnd (TCForall C (env_to_list Γp)) (TCEq Γp Γp')
  | AIEnvFilter C => FilterPersistentEnv M C Γp Γp'
  | AIEnvIsEmpty => TCAnd (TCEq Γp Enil) (TCEq Γp' Enil)
  | AIEnvClear => TCEq Γp' Enil
  | AIEnvId => TCEq Γp Γp'
  end →
  match always_modality_spatial_spec M with
  | AIEnvForall C => TCAnd (TCForall C (env_to_list Γs)) (TCEq Γs Γs')
  | AIEnvFilter C => FilterSpatialEnv M C Γs Γs'
  | AIEnvIsEmpty => TCAnd (TCEq Γs Enil) (TCEq Γs' Enil)
  | AIEnvClear => TCEq Γs' Enil
  | AIEnvId => TCEq Γs Γs'
  end →
  envs_entails (Envs Γp' Γs') Q → envs_entails (Envs Γp Γs) Q'.
Proof.
  rewrite envs_entails_eq /FromAlways /of_envs /= => <- HΓp HΓs <-.
  apply pure_elim_l=> -[???]. assert (envs_wf (Envs Γp' Γs')).
  { split; simpl in *.
    - destruct (always_modality_persistent_spec M); tac_always_cases.
    - destruct (always_modality_spatial_spec M); tac_always_cases.
    - destruct (always_modality_persistent_spec M),
        (always_modality_spatial_spec M); tac_always_cases; naive_solver. }
  rewrite pure_True // left_id. rewrite -always_modality_sep. apply sep_mono.
  - destruct (always_modality_persistent_spec M) eqn:?; tac_always_cases.
    + by rewrite {1}affinely_elim_emp (always_modality_emp M)
        persistently_True_emp affinely_persistently_emp.
    + eauto using always_modality_persistent_forall_big_and.
    + eauto using always_modality_persistent_filter.
    + by rewrite {1}affinely_elim_emp (always_modality_emp M)
        persistently_True_emp affinely_persistently_emp.
    + eauto using always_modality_persistent_id.
  - destruct (always_modality_spatial_spec M) eqn:?; tac_always_cases.
    + by rewrite -always_modality_emp.
    + eauto using always_modality_spatial_forall_big_sep.
    + eauto using always_modality_spatial_filter,
        always_modality_spatial_filter_absorbing.
    + rewrite -(always_modality_spatial_clear M) // -always_modality_emp.
      by rewrite -absorbingly_True_emp absorbingly_pure -True_intro.
    + by destruct (always_modality_spatial_id M).
Qed.

Lemma tac_persistent Δ Δ' i p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPersistent p P P' →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  envs_replace i p true (Esnoc Enil i P') Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=>?? HPQ ? HQ. rewrite envs_replace_singleton_sound //=.
  destruct p; simpl.
  - by rewrite -(into_persistent _ P) /= wand_elim_r.
  - destruct HPQ.
    + rewrite -(affine_affinely P) (_ : P = bi_persistently_if false P)%I //
              (into_persistent _ P) wand_elim_r //.
    + rewrite (_ : P = bi_persistently_if false P)%I // (into_persistent _ P).
      by rewrite {1}(persistent_absorbingly_affinely (bi_persistently _)%I)
                 absorbingly_sep_l wand_elim_r HQ.
Qed.

(** * Implication and wand *)
Lemma envs_app_singleton_sound_foo Δ Δ' p j Q :
  envs_app p (Esnoc Enil j Q) Δ = Some Δ' → of_envs Δ ∗ □?p Q ⊢ of_envs Δ'.
Proof. intros. apply wand_elim_l'. eapply envs_app_singleton_sound. eauto. Qed.

Lemma tac_impl_intro Δ Δ' i P P' Q R :
  FromImpl R P Q →
  (if env_spatial_is_nil Δ then TCTrue else Persistent P) →
  envs_app false (Esnoc Enil i P') Δ = Some Δ' →
  FromAffinely P' P →
  envs_entails Δ' Q → envs_entails Δ R.
Proof.
  rewrite /FromImpl envs_entails_eq => <- ??? <-. destruct (env_spatial_is_nil Δ) eqn:?.
  - rewrite (env_spatial_is_nil_affinely_persistently Δ) //; simpl. apply impl_intro_l.
    rewrite envs_app_singleton_sound //; simpl.
    rewrite -(from_affinely P') -affinely_and_lr.
    by rewrite persistently_and_affinely_sep_r affinely_persistently_elim wand_elim_r.
  - apply impl_intro_l. rewrite envs_app_singleton_sound //; simpl.
    by rewrite -(from_affinely P') persistent_and_affinely_sep_l_1 wand_elim_r.
Qed.
Lemma tac_impl_intro_persistent Δ Δ' i P P' Q R :
  FromImpl R P Q →
  IntoPersistent false P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ R.
Proof.
  rewrite /FromImpl envs_entails_eq => <- ?? <-.
  rewrite envs_app_singleton_sound //=. apply impl_intro_l.
  rewrite (_ : P = bi_persistently_if false P)%I // (into_persistent false P).
  by rewrite persistently_and_affinely_sep_l wand_elim_r.
Qed.
Lemma tac_impl_intro_drop Δ P Q R :
  FromImpl R P Q → envs_entails Δ Q → envs_entails Δ R.
Proof.
  rewrite /FromImpl envs_entails_eq => <- ?. apply impl_intro_l. by rewrite and_elim_r.
Qed.

Lemma tac_wand_intro Δ Δ' i P Q R :
  FromWand R P Q →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ R.
Proof.
  rewrite /FromWand envs_entails_eq => <- ? HQ.
  rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.
Lemma tac_wand_intro_persistent Δ Δ' i P P' Q R :
  FromWand R P Q →
  IntoPersistent false P P' →
  TCOr (Affine P) (Absorbing Q) →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ R.
Proof.
  rewrite /FromWand envs_entails_eq => <- ? HPQ ? HQ.
  rewrite envs_app_singleton_sound //=. apply wand_intro_l. destruct HPQ.
  - rewrite -(affine_affinely P) (_ : P = bi_persistently_if false P)%I //
            (into_persistent _ P) wand_elim_r //.
  - rewrite (_ : P = □?false P)%I // (into_persistent _ P).
    by rewrite {1}(persistent_absorbingly_affinely (bi_persistently _)%I)
               absorbingly_sep_l wand_elim_r HQ.
Qed.
Lemma tac_wand_intro_pure Δ P φ Q R :
  FromWand R P Q →
  IntoPure P φ →
  TCOr (Affine P) (Absorbing Q) →
  (φ → envs_entails Δ Q) → envs_entails Δ R.
Proof.
  rewrite /FromWand envs_entails_eq. intros <- ? HPQ HQ. apply wand_intro_l. destruct HPQ.
  - rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
    by apply pure_elim_l.
  - rewrite (into_pure P) (persistent_absorbingly_affinely ⌜ _ ⌝%I) absorbingly_sep_lr.
    rewrite -persistent_and_affinely_sep_l. apply pure_elim_l=> ?. by rewrite HQ.
Qed.
Lemma tac_wand_intro_drop Δ P Q R :
  FromWand R P Q →
  TCOr (Affine P) (Absorbing Q) →
  envs_entails Δ Q →
  envs_entails Δ R.
Proof.
  rewrite envs_entails_eq /FromWand => <- HPQ ->. apply wand_intro_l. by rewrite sep_elim_r.
Qed.

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
  envs_entails Δ'' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ??? <-. destruct p.
  - rewrite envs_lookup_persistent_sound //.
    rewrite envs_simple_replace_singleton_sound //; simpl.
    rewrite -affinely_persistently_if_idemp -affinely_persistently_idemp into_wand /=.
    rewrite assoc (affinely_persistently_affinely_persistently_if q).
    by rewrite affinely_persistently_if_sep_2 wand_elim_r wand_elim_r.
  - rewrite envs_lookup_sound //; simpl.
    rewrite envs_lookup_sound // (envs_replace_singleton_sound' _ Δ'') //; simpl.
    by rewrite into_wand /= assoc wand_elim_r wand_elim_r.
Qed.

Lemma tac_specialize_assert Δ Δ' Δ1 Δ2' j q neg js R P1 P2 P1' Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q false R P1 P2 → AddModal P1' P1 Q →
  (''(Δ1,Δ2) ← envs_split (if neg is true then Right else Left) js Δ';
    Δ2' ← envs_app false (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2')) = Some (Δ1,Δ2') → (* does not preserve position of [j] *)
  envs_entails Δ1 P1' → envs_entails Δ2' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ??? HP1 HQ.
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl.
  rewrite HP1 into_wand /= -(add_modal P1' P1 Q). cancel [P1'].
  apply wand_intro_l. by rewrite assoc !wand_elim_r.
Qed.

Lemma tac_unlock Δ Q : envs_entails Δ Q → envs_entails Δ (locked Q).
Proof. by unlock. Qed.

Lemma tac_specialize_frame Δ Δ' j q R P1 P2 P1' Q Q' :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q false R P1 P2 →
  AddModal P1' P1 Q →
  envs_entails Δ' (P1' ∗ locked Q') →
  Q' = (P2 -∗ Q)%I →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ?? HPQ ->.
  rewrite envs_lookup_sound //. rewrite HPQ -lock.
  rewrite into_wand -{2}(add_modal P1' P1 Q). cancel [P1'].
  apply wand_intro_l. by rewrite assoc !wand_elim_r.
Qed.

Lemma tac_specialize_assert_pure Δ Δ' j q R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q true R P1 P2 →
  FromPure true P1 φ →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ' →
  φ → envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ????? <-. rewrite envs_simple_replace_singleton_sound //=.
  rewrite -affinely_persistently_if_idemp into_wand /= -(from_pure _ P1).
  rewrite pure_True //= persistently_affinely persistently_pure
          affinely_True_emp affinely_emp.
  by rewrite emp_wand wand_elim_r.
Qed.

Lemma tac_specialize_assert_persistent Δ Δ' Δ'' j q P1 P1' P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand q true R P1 P2 →
  Persistent P1 →
  IntoAbsorbingly P1' P1 →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ'' →
  envs_entails Δ' P1' → envs_entails Δ'' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => /envs_lookup_delete_Some [? ->] ???? HP1 <-.
  rewrite envs_lookup_sound //.
  rewrite -(idemp bi_and (of_envs (envs_delete _ _ _))).
  rewrite {2}envs_simple_replace_singleton_sound' //; simpl.
  rewrite {1}HP1 (into_absorbingly P1') (persistent_persistently_2 P1).
  rewrite absorbingly_persistently persistently_and_affinely_sep_l assoc.
  rewrite -affinely_persistently_if_idemp -affinely_persistently_idemp.
  rewrite (affinely_persistently_affinely_persistently_if q).
  by rewrite affinely_persistently_if_sep_2 into_wand wand_elim_l wand_elim_r.
Qed.

Lemma tac_specialize_persistent_helper Δ Δ'' j q P R R' Q :
  envs_lookup j Δ = Some (q,P) →
  envs_entails Δ (bi_absorbingly R) →
  IntoPersistent false R R' →
  (if q then TCTrue else BiAffine PROP) →
  envs_replace j q true (Esnoc Enil j R') Δ = Some Δ'' →
  envs_entails Δ'' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ? HR ? Hpos ? <-. rewrite -(idemp bi_and (of_envs Δ)) {1}HR.
  rewrite envs_replace_singleton_sound //; destruct q; simpl.
  - by rewrite (_ : R = bi_persistently_if false R)%I // (into_persistent _ R)
      absorbingly_persistently sep_elim_r persistently_and_affinely_sep_l wand_elim_r.
  - by rewrite (absorbing_absorbingly R) (_ : R = bi_persistently_if false R)%I //
       (into_persistent _ R) sep_elim_r persistently_and_affinely_sep_l wand_elim_r.
Qed.

Lemma tac_revert Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  envs_entails Δ' ((if p then □ P else P)%I -∗ Q) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ? HQ. rewrite envs_lookup_delete_sound //=.
  rewrite HQ. destruct p; simpl; auto using wand_elim_r.
Qed.

Class IntoIH {PROP : bi} (φ : Prop) (Δ : envs PROP) (Q : PROP) :=
  into_ih : φ → of_envs Δ ⊢ Q.
Global Instance into_ih_entails Δ Q : IntoIH (envs_entails Δ Q) Δ Q.
Proof. by rewrite envs_entails_eq /IntoIH. Qed.
Global Instance into_ih_forall {A} (φ : A → Prop) Δ Φ :
  (∀ x, IntoIH (φ x) Δ (Φ x)) → IntoIH (∀ x, φ x) Δ (∀ x, Φ x)%I | 2.
Proof. rewrite /IntoIH=> HΔ ?. apply forall_intro=> x. by rewrite (HΔ x). Qed.
Global Instance into_ih_impl (φ ψ : Prop) Δ Q :
  IntoIH φ Δ Q → IntoIH (ψ → φ) Δ (⌜ψ⌝ → Q)%I | 1.
Proof. rewrite /IntoIH=> HΔ ?. apply impl_intro_l, pure_elim_l. auto. Qed.

Lemma tac_revert_ih Δ P Q {φ : Prop} (Hφ : φ) :
  IntoIH φ Δ P →
  env_spatial_is_nil Δ = true →
  envs_entails Δ (bi_persistently P → Q) →
  envs_entails Δ Q.
Proof.
  rewrite /IntoIH envs_entails_eq. intros HP ? HPQ.
  rewrite (env_spatial_is_nil_affinely_persistently Δ) //.
  rewrite -(idemp bi_and (□ (of_envs Δ))%I) {1}HP // HPQ.
  by rewrite -{1}persistently_idemp !affinely_persistently_elim impl_elim_r.
Qed.

Lemma tac_assert Δ Δ1 Δ2 Δ2' neg js j P P' Q :
  AddModal P' P Q →
  envs_split (if neg is true then Right else Left) js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ2 = Some Δ2' →
  envs_entails Δ1 P' → envs_entails Δ2' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=>??? HP HQ. rewrite envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl. by rewrite HP HQ.
Qed.

Lemma tac_assert_persistent Δ Δ1 Δ2 Δ' neg js j P P' Q :
  envs_split (if neg is true then Right else Left) js Δ = Some (Δ1,Δ2) →
  Persistent P →
  FromAffinely P' P →
  envs_app false (Esnoc Enil j P') Δ = Some Δ' →
  envs_entails Δ1 P → envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ???? HP <-.
  rewrite -(idemp bi_and (of_envs Δ)) {1}envs_split_sound //.
  rewrite HP. rewrite (persistent_persistently_2 P) sep_elim_l.
  rewrite persistently_and_affinely_sep_l -affinely_idemp.
  rewrite affinely_persistently_elim from_affinely envs_app_singleton_sound //=.
  by rewrite wand_elim_r.
Qed.

Lemma tac_assert_pure Δ Δ' j P P' φ Q :
  FromPure true P φ →
  FromAffinely P' P →
  envs_app false (Esnoc Enil j P') Δ = Some Δ' →
  φ → envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ???? <-. rewrite envs_app_singleton_sound //=.
  rewrite -(from_affinely P') -(from_pure _ P) pure_True //.
  by rewrite affinely_idemp affinely_True_emp affinely_emp emp_wand.
Qed.

Lemma tac_pose_proof Δ Δ' j P Q :
  P →
  envs_app true (Esnoc Enil j P) Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => HP ? <-. rewrite envs_app_singleton_sound //=.
  by rewrite -HP /= affinely_persistently_emp emp_wand.
Qed.

Lemma tac_pose_proof_hyp Δ Δ' Δ'' i p j P Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  envs_app p (Esnoc Enil j P) (if p then Δ else Δ') = Some Δ'' →
  envs_entails Δ'' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_app_singleton_sound //=.
    by rewrite wand_elim_r.
  - rewrite envs_lookup_sound // envs_app_singleton_sound //=.
    by rewrite wand_elim_r.
Qed.

Lemma tac_apply Δ Δ' i p R P1 P2 :
  envs_lookup_delete i Δ = Some (p, R, Δ') →
  IntoWand p false R P1 P2 →
  envs_entails Δ' P1 → envs_entails Δ P2.
Proof.
  rewrite envs_entails_eq => ?? HP1. rewrite envs_lookup_delete_sound //.
  by rewrite into_wand /= HP1 wand_elim_l.
Qed.

(** * Conjunction splitting *)
Lemma tac_and_split Δ P Q1 Q2 :
  FromAnd P Q1 Q2 → envs_entails Δ Q1 → envs_entails Δ Q2 → envs_entails Δ P.
Proof. rewrite envs_entails_eq. intros. rewrite -(from_and P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Lemma tac_sep_split Δ Δ1 Δ2 d js P Q1 Q2 :
  FromSep P Q1 Q2 →
  envs_split d js Δ = Some (Δ1,Δ2) →
  envs_entails Δ1 Q1 → envs_entails Δ2 Q2 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=>?? HQ1 HQ2.
  rewrite envs_split_sound //. by rewrite HQ1 HQ2.
Qed.

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
  envs_entails Δ3 Q → envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_eq => ??? <-. rewrite envs_lookup_delete_list_sound //.
  rewrite from_seps. rewrite envs_app_singleton_sound //=.
  by rewrite wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Lemma tac_and_destruct Δ Δ' i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd true P P1 P2 else IntoSep P P1 P2) →
  envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros. rewrite envs_simple_replace_sound //=. destruct p.
  - by rewrite (into_and _ P) /= right_id -(comm _ P1) wand_elim_r.
  - by rewrite /= (into_sep P) right_id -(comm _ P1) wand_elim_r.
Qed.

(* Using this tactic, one can destruct a (non-separating) conjunction in the
spatial context as long as one of the conjuncts is thrown away. It corresponds
to the principle of "external choice" in linear logic. *)
Lemma tac_and_destruct_choice Δ Δ' i p d j P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd p P P1 P2 : Type else
    TCOr (IntoAnd p P P1 P2) (TCAnd (IntoSep P P1 P2)
      (if d is Left then TCOr (Affine P2) (Absorbing Q)
       else TCOr (Affine P1) (Absorbing Q)))) →
  envs_simple_replace i p (Esnoc Enil j (if d is Left then P1 else P2)) Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ? HP ? HQ.
  rewrite envs_simple_replace_singleton_sound //=. destruct p.
  { rewrite (into_and _ P) HQ. destruct d; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  destruct HP as [?|[??]].
  { rewrite (into_and _ P) HQ. destruct d; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  rewrite (into_sep P) HQ. destruct d; simpl.
  - by rewrite (comm _ P1) -assoc wand_elim_r sep_elim_r.
  - by rewrite -assoc wand_elim_r sep_elim_r.
Qed.

(** * Framing *)
Lemma tac_frame_pure Δ (φ : Prop) P Q :
  φ → Frame true ⌜φ⌝ P Q → envs_entails Δ Q → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq => ?? ->. rewrite -(frame ⌜φ⌝ P) /=.
  rewrite -persistently_and_affinely_sep_l persistently_pure.
  auto using and_intro, pure_intro.
Qed.

Lemma tac_frame Δ Δ' i p R P Q :
  envs_lookup_delete i Δ = Some (p, R, Δ') →
  Frame p R P Q →
  envs_entails (if p then Δ else Δ') Q → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ? HQ. destruct p.
  - by rewrite envs_lookup_persistent_sound // -(frame R P) HQ.
  - rewrite envs_lookup_sound //; simpl. by rewrite -(frame R P) HQ.
Qed.

(** * Disjunction *)
Lemma tac_or_l Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q1 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_l'.
Qed.
Lemma tac_or_r Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q2 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_r'.
Qed.

Lemma tac_or_destruct Δ Δ1 Δ2 i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j1 P1) Δ = Some Δ1 →
  envs_simple_replace i p (Esnoc Enil j2 P2) Δ = Some Δ2 →
  envs_entails Δ1 Q → envs_entails Δ2 Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ???? HP1 HP2. rewrite envs_lookup_sound //.
  rewrite (into_or P) affinely_persistently_if_or sep_or_r; apply or_elim.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ1) //.
    by rewrite wand_elim_r.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ2) //.
    by rewrite wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → PROP) Q :
  FromForall Q Φ →
  (∀ a, envs_entails Δ (Φ a)) →
  envs_entails Δ Q.
Proof. rewrite envs_entails_eq /FromForall=> <-. apply forall_intro. Qed.

Lemma tac_forall_specialize {A} Δ Δ' i p P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoForall P Φ →
  (∃ x : A,
    envs_simple_replace i p (Esnoc Enil i (Φ x)) Δ = Some Δ' ∧
    envs_entails Δ' Q) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ?? (x&?&?).
  rewrite envs_simple_replace_singleton_sound //; simpl.
  by rewrite (into_forall P) (forall_elim x) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → PROP) :
  envs_entails Δ (∀ a, Φ a) → ∀ a, envs_entails Δ (Φ a).
Proof. rewrite envs_entails_eq => HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Lemma tac_exist {A} Δ P (Φ : A → PROP) :
  FromExist P Φ → (∃ a, envs_entails Δ (Φ a)) → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq => ? [a ?].
  rewrite -(from_exist P). eauto using exist_intro'.
Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ →
  (∀ a, ∃ Δ',
    envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ = Some Δ' ∧
    envs_entails Δ' Q) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) affinely_persistently_if_exist sep_exist_r.
  apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
  rewrite envs_simple_replace_singleton_sound' //; simpl. by rewrite wand_elim_r.
Qed.

(** * Modalities *)
Lemma tac_modal_intro Δ P Q :
  FromModal P Q → envs_entails Δ Q → envs_entails Δ P.
Proof. by rewrite envs_entails_eq /FromModal=> <- ->. Qed.

Lemma tac_modal_elim Δ Δ' i p φ P' P Q Q' :
  envs_lookup i Δ = Some (p, P) →
  ElimModal φ P P' Q Q' →
  φ →
  envs_replace i p false (Esnoc Enil i P') Δ = Some Δ' →
  envs_entails Δ' Q' → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ???? HΔ. rewrite envs_replace_singleton_sound //=.
  rewrite HΔ affinely_persistently_if_elim. by eapply elim_modal.
Qed.
End bi_tactics.

Section sbi_tactics.
Context {PROP : sbi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

(** * Rewriting *)
Lemma tac_rewrite Δ i p Pxy d Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : ofeT} (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (Q ⊣⊢ Φ (if d is Left then y else x)) →
    NonExpansive Φ →
    envs_entails Δ (Φ (if d is Left then x else y)) → envs_entails Δ Q.
Proof.
  intros ? A x y ? HPxy -> ?. rewrite envs_entails_eq.
  apply internal_eq_rewrite'; auto. rewrite {1}envs_lookup_sound //.
  rewrite (into_internal_eq Pxy x y) affinely_persistently_if_elim sep_elim_l.
  destruct d; auto using internal_eq_sym.
Qed.

Lemma tac_rewrite_in Δ i p Pxy j q P d Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P) →
  ∀ {A : ofeT} Δ' (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (P ⊣⊢ Φ (if d is Left then y else x)) →
    NonExpansive Φ →
    envs_simple_replace j q (Esnoc Enil j (Φ (if d is Left then x else y))) Δ = Some Δ' →
    envs_entails Δ' Q →
    envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq /IntoInternalEq => ?? A Δ' x y Φ HPxy HP ?? <-.
  rewrite -(idemp bi_and (of_envs Δ)) {2}(envs_lookup_sound _ i) //.
  rewrite (envs_simple_replace_singleton_sound _ _ j) //=.
  rewrite HP HPxy (affinely_persistently_if_elim _ (_ ≡ _)%I) sep_elim_l.
  rewrite persistent_and_affinely_sep_r -assoc. apply wand_elim_r'.
  rewrite -persistent_and_affinely_sep_r. apply impl_elim_r'. destruct d.
  - apply (internal_eq_rewrite x y (λ y, □?q Φ y -∗ of_envs Δ')%I). solve_proper.
  - rewrite internal_eq_sym.
    eapply (internal_eq_rewrite y x (λ y, □?q Φ y -∗ of_envs Δ')%I). solve_proper.
Qed.

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
  IntoLaterNEnvs n Δ1 Δ2 → of_envs Δ1 ⊢ ▷^n (of_envs Δ2).
Proof.
  intros [Hp Hs]; rewrite /of_envs /= !laterN_and !laterN_sep.
  rewrite -{1}laterN_intro -laterN_affinely_persistently_2.
  apply and_mono, sep_mono.
  - apply pure_mono; destruct 1; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - apply affinely_mono, persistently_mono.
    induction Hp; rewrite /= ?laterN_and. apply laterN_intro. by apply and_mono.
  - induction Hs; rewrite /= ?laterN_sep. apply laterN_intro. by apply sep_mono.
Qed.

Lemma tac_next Δ Δ' n Q Q' :
  FromLaterN n Q Q' → IntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' Q' → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HQ.
    by rewrite -(from_laterN n Q) into_laterN_env_sound HQ.
Qed.

Lemma tac_löb Δ Δ' i Q :
  env_spatial_is_nil Δ = true →
  envs_app true (Esnoc Enil i (▷ Q)%I) Δ = Some Δ' →
  envs_entails Δ' Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HQ.
  rewrite (env_spatial_is_nil_affinely_persistently Δ) //.
  rewrite -(persistently_and_emp_elim Q). apply and_intro; first apply: affine.
  rewrite -(löb (bi_persistently Q)%I) later_persistently. apply impl_intro_l.
  rewrite envs_app_singleton_sound //; simpl; rewrite HQ.
  rewrite persistently_and_affinely_sep_l -{1}affinely_persistently_idemp.
  by rewrite affinely_persistently_sep_2 wand_elim_r affinely_elim.
Qed.
End sbi_tactics.
