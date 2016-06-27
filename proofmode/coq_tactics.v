From iris.algebra Require Export upred.
From iris.algebra Require Import upred_big_op upred_tactics gmap.
From iris.proofmode Require Export environments.
From iris.prelude Require Import stringmap hlist.
Import uPred.

Local Notation "Γ !! j" := (env_lookup j Γ).
Local Notation "x ← y ; z" := (match y with Some x => z | None => None end).
Local Notation "' ( x1 , x2 ) ← y ; z" :=
  (match y with Some (x1,x2) => z | None => None end).
Local Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (match y with Some (x1,x2,x3) => z | None => None end).

Record envs (M : ucmraT) :=
  Envs { env_persistent : env (uPred M); env_spatial : env (uPred M) }.
Add Printing Constructor envs.
Arguments Envs {_} _ _.
Arguments env_persistent {_} _.
Arguments env_spatial {_} _.

Record envs_wf {M} (Δ : envs M) := {
  env_persistent_valid : env_wf (env_persistent Δ);
  env_spatial_valid : env_wf (env_spatial Δ);
  envs_disjoint i : env_persistent Δ !! i = None ∨ env_spatial Δ !! i = None
}.

Coercion of_envs {M} (Δ : envs M) : uPred M :=
  (■ envs_wf Δ ★ □ [∧] env_persistent Δ ★ [★] env_spatial Δ)%I.
Instance: Params (@of_envs) 1.

Record envs_Forall2 {M} (R : relation (uPred M)) (Δ1 Δ2 : envs M) : Prop := {
  env_persistent_Forall2 : env_Forall2 R (env_persistent Δ1) (env_persistent Δ2);
  env_spatial_Forall2 : env_Forall2 R (env_spatial Δ1) (env_spatial Δ2)
}.

Definition envs_dom {M} (Δ : envs M) : list string :=
  env_dom (env_persistent Δ) ++ env_dom (env_spatial Δ).

Definition envs_lookup {M} (i : string) (Δ : envs M) : option (bool * uPred M) :=
  let (Γp,Γs) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P) | None => P ← env_lookup i Γs; Some (false, P)
  end.

Definition envs_delete {M} (i : string) (p : bool) (Δ : envs M) : envs M :=
  let (Γp,Γs) := Δ in
  match p with
  | true => Envs (env_delete i Γp) Γs | false => Envs Γp (env_delete i Γs)
  end.

Definition envs_lookup_delete {M} (i : string)
    (Δ : envs M) : option (bool * uPred M * envs M) :=
  let (Γp,Γs) := Δ in
  match env_lookup_delete i Γp with
  | Some (P,Γp') => Some (true, P, Envs Γp' Γs)
  | None => '(P,Γs') ← env_lookup_delete i Γs; Some (false, P, Envs Γp Γs')
  end.

Definition envs_app {M} (p : bool)
    (Γ : env (uPred M)) (Δ : envs M) : option (envs M) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_simple_replace {M} (i : string) (p : bool) (Γ : env (uPred M))
    (Δ : envs M) : option (envs M) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_replace {M} (i : string) (p q : bool) (Γ : env (uPred M))
    (Δ : envs M) : option (envs M) :=
  if eqb p q then envs_simple_replace i p Γ Δ
  else envs_app q Γ (envs_delete i p Δ).

(* if [lr = false] then [result = (hyps named js, remaining hyps)],
   if [lr = true] then [result = (remaining hyps, hyps named js)] *)
Definition envs_split {M}
    (lr : bool) (js : list string) (Δ : envs M) : option (envs M * envs M) :=
  let (Γp,Γs) := Δ in
  '(Γs1,Γs2) ← env_split js Γs;
  match lr with
  | false  => Some (Envs Γp Γs1, Envs Γp Γs2)
  | true => Some (Envs Γp Γs2, Envs Γp Γs1)
  end.

Definition envs_persistent {M} (Δ : envs M) :=
  if env_spatial Δ is Enil then true else false.

Definition envs_clear_spatial {M} (Δ : envs M) : envs M :=
  Envs (env_persistent Δ) Enil.

(* Coq versions of the tactics *)
Section tactics.
Context {M : ucmraT}.
Implicit Types Γ : env (uPred M).
Implicit Types Δ : envs M.
Implicit Types P Q : uPred M.

Lemma of_envs_def Δ :
  of_envs Δ = (■ envs_wf Δ ★ □ [∧] env_persistent Δ ★ [★] env_spatial Δ)%I.
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
  envs_lookup i Δ = Some (p,P) → Δ ⊢ □?p P ★ envs_delete i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /of_envs=>?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_and_sep always_sep.
    ecancel [□ [∧] _; □ P; [★] _]%I; apply pure_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=.
    ecancel [□ [∧] _; P; [★] _]%I; apply pure_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
Qed.
Lemma envs_lookup_sound' Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ P ★ envs_delete i p Δ.
Proof. intros. rewrite envs_lookup_sound //. by rewrite always_if_elim. Qed.
Lemma envs_lookup_persistent_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → Δ ⊢ □ P ★ Δ.
Proof.
  intros. apply: always_entails_l. by rewrite envs_lookup_sound // sep_elim_l.
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ □?p P ★ (□?p P -★ Δ).
Proof.
  rewrite /envs_lookup /of_envs=>?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_and_sep always_sep.
    rewrite pure_equiv // left_id.
    cancel [□ P]%I. apply wand_intro_l. solve_sep_entails.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=. rewrite pure_equiv // left_id.
    cancel [P]. apply wand_intro_l. solve_sep_entails.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ □?p P ★ Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound. Qed.
Lemma envs_lookup_delete_sound' Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ P ★ Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound'. Qed.

Lemma envs_app_sound Δ Δ' p Γ : envs_app p Γ Δ = Some Δ' → Δ ⊢ □?p [★] Γ -★ Δ'.
Proof.
  rewrite /of_envs /envs_app=> ?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_and_app always_and_sep always_sep (big_sep_and Γ).
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γs') // big_sep_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ □?p [★] Γ -★ Δ'.
Proof.
  rewrite /envs_simple_replace /envs_delete /of_envs=> ?.
  apply pure_elim_sep_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_and_app always_and_sep always_sep (big_sep_and Γ).
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_sep_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  Δ ⊢ □?p P ★ (□?p [★] Γ -★ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' → envs_delete i p Δ ⊢ □?q [★] Γ -★ Δ'.
Proof.
  rewrite /envs_replace; destruct (eqb _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  Δ ⊢ □?p P ★ (□?q [★] Γ -★ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_split_sound Δ lr js Δ1 Δ2 :
  envs_split lr js Δ = Some (Δ1,Δ2) → Δ ⊢ Δ1 ★ Δ2.
Proof.
  rewrite /envs_split /of_envs=> ?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (env_split js _) as [[Γs1 Γs2]|] eqn:?; simplify_eq/=.
  rewrite (env_split_perm Γs) // big_sep_app {1}always_sep_dup'.
  destruct lr; simplify_eq/=; cancel [□ [∧] Γp; □ [∧] Γp; [★] Γs1; [★] Γs2]%I;
    destruct Hwf; apply sep_intro_True_l; apply pure_intro; constructor;
      naive_solver eauto using env_split_wf_1, env_split_wf_2,
      env_split_fresh_1, env_split_fresh_2.
Qed.

Lemma envs_clear_spatial_sound Δ : Δ ⊢ envs_clear_spatial Δ ★ [★] env_spatial Δ.
Proof.
  rewrite /of_envs /envs_clear_spatial /=; apply pure_elim_sep_l=> Hwf.
  rewrite right_id -assoc; apply sep_intro_True_l; [apply pure_intro|done].
  destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_fold_wand Γ Q : env_fold uPred_wand Q Γ ⊣⊢ ([★] Γ -★ Q).
Proof.
  revert Q; induction Γ as [|Γ IH i P]=> Q /=; [by rewrite wand_True|].
  by rewrite IH wand_curry (comm uPred_sep).
Qed.

Lemma envs_persistent_persistent Δ : envs_persistent Δ = true → PersistentP Δ.
Proof. intros; destruct Δ as [? []]; simplify_eq/=; apply _. Qed.
Hint Immediate envs_persistent_persistent : typeclass_instances.

Global Instance envs_Forall2_refl (R : relation (uPred M)) :
  Reflexive R → Reflexive (envs_Forall2 R).
Proof. by constructor. Qed.
Global Instance envs_Forall2_sym (R : relation (uPred M)) :
  Symmetric R → Symmetric (envs_Forall2 R).
Proof. intros ??? [??]; by constructor. Qed.
Global Instance envs_Forall2_trans (R : relation (uPred M)) :
  Transitive R → Transitive (envs_Forall2 R).
Proof. intros ??? [??] [??] [??]; constructor; etrans; eauto. Qed.
Global Instance envs_Forall2_antisymm (R R' : relation (uPred M)) :
  AntiSymm R R' → AntiSymm (envs_Forall2 R) (envs_Forall2 R').
Proof. intros ??? [??] [??]; constructor; by eapply (anti_symm _). Qed.
Lemma envs_Forall2_impl (R R' : relation (uPred M)) Δ1 Δ2 :
  envs_Forall2 R Δ1 Δ2 → (∀ P Q, R P Q → R' P Q) → envs_Forall2 R' Δ1 Δ2.
Proof. intros [??] ?; constructor; eauto using env_Forall2_impl. Qed.

Global Instance of_envs_mono : Proper (envs_Forall2 (⊢) ==> (⊢)) (@of_envs M).
Proof.
  intros [Γp1 Γs1] [Γp2 Γs2] [Hp Hs]; unfold of_envs; simpl in *.
  apply pure_elim_sep_l=>Hwf. apply sep_intro_True_l.
  - destruct Hwf; apply pure_intro; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - by repeat f_equiv.
Qed.
Global Instance of_envs_proper : Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢)) (@of_envs M).
Proof.
  intros Δ1 Δ2 ?; apply (anti_symm (⊢)); apply of_envs_mono;
    eapply envs_Forall2_impl; [| |symmetry|]; eauto using equiv_entails.
Qed.
Global Instance Envs_mono (R : relation (uPred M)) :
  Proper (env_Forall2 R ==> env_Forall2 R ==> envs_Forall2 R) (@Envs M).
Proof. by constructor. Qed.

(** * Adequacy *)
Lemma tac_adequate P : (Envs Enil Enil ⊢ P) → True ⊢ P.
Proof.
  intros <-. rewrite /of_envs /= always_pure !right_id.
  apply pure_intro; repeat constructor.
Qed.

(** * Basic rules *)
Class FromAssumption (p : bool) (P Q : uPred M) := from_assumption : □?p P ⊢ Q.
Arguments from_assumption _ _ _ {_}.
Global Instance from_assumption_exact p P : FromAssumption p P P.
Proof. destruct p; by rewrite /FromAssumption /= ?always_elim. Qed.
Global Instance from_assumption_always_l p P Q :
  FromAssumption p P Q → FromAssumption p (□ P) Q.
Proof. rewrite /FromAssumption=><-. by rewrite always_elim. Qed.
Global Instance from_assumption_always_r P Q :
  FromAssumption true P Q → FromAssumption true P (□ Q).
Proof. rewrite /FromAssumption=><-. by rewrite always_always. Qed.

Lemma tac_assumption Δ i p P Q :
  envs_lookup i Δ = Some (p,P) → FromAssumption p P Q → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_sound // sep_elim_l. Qed.

Lemma tac_rename Δ Δ' i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //.
  destruct p; simpl; by rewrite right_id wand_elim_r.
Qed.
Lemma tac_clear Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_delete_sound // sep_elim_r. Qed.
Lemma tac_clear_spatial Δ Δ' Q :
  envs_clear_spatial Δ = Δ' → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof. intros <- ?. by rewrite envs_clear_spatial_sound // sep_elim_l. Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : (Δ ⊢ False) → Δ ⊢ Q.
Proof. by rewrite -(False_elim Q). Qed.

(** * Pure *)
Class IsPure (P : uPred M) (φ : Prop) := is_pure : P ⊣⊢ ■ φ.
Arguments is_pure : clear implicits.
Global Instance is_pure_pure φ : IsPure (■ φ) φ.
Proof. done. Qed.
Global Instance is_pure_eq {A : cofeT} (a b : A) :
  Timeless a → IsPure (a ≡ b) (a ≡ b).
Proof. intros; red. by rewrite timeless_eq. Qed.
Global Instance is_pure_valid `{CMRADiscrete A} (a : A) : IsPure (✓ a) (✓ a).
Proof. intros; red. by rewrite discrete_valid. Qed.

Lemma tac_pure_intro Δ Q (φ : Prop) : IsPure Q φ → φ → Δ ⊢ Q.
Proof. intros ->. apply pure_intro. Qed.

Lemma tac_pure Δ Δ' i p P φ Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') → IsPure P φ →
  (φ → Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite envs_lookup_delete_sound' //; simpl.
  rewrite (is_pure P); by apply pure_elim_sep_l.
Qed.

Lemma tac_pure_revert Δ φ Q : (Δ ⊢ ■ φ → Q) → (φ → Δ ⊢ Q).
Proof. intros HΔ ?. by rewrite HΔ pure_equiv // left_id. Qed.

(** * Later *)
Class IntoLater (P Q : uPred M) := into_later : P ⊢ ▷ Q.
Arguments into_later _ _ {_}.
Class FromLater (P Q : uPred M) := from_later : ▷ Q ⊢ P.
Arguments from_later _ _ {_}.
Class IntoLaterEnv (Γ1 Γ2 : env (uPred M)) :=
  into_later_env : env_Forall2 IntoLater Γ1 Γ2.
Class IntoLaterEnvs (Δ1 Δ2 : envs M) := {
  into_later_persistent: IntoLaterEnv (env_persistent Δ1) (env_persistent Δ2);
  into_later_spatial: IntoLaterEnv (env_spatial Δ1) (env_spatial Δ2)
}.

Global Instance into_later_fallthrough P : IntoLater P P | 1000.
Proof. apply later_intro. Qed.
Global Instance into_later_later P : IntoLater (▷ P) P.
Proof. done. Qed.
Global Instance into_later_and P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite later_and; apply and_mono. Qed.
Global Instance into_later_or P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite later_or; apply or_mono. Qed.
Global Instance into_later_sep P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ★ P2) (Q1 ★ Q2).
Proof. intros ??; red. by rewrite later_sep; apply sep_mono. Qed.

Global Instance into_later_big_sepM `{Countable K} {A}
    (Φ Ψ : K → A → uPred M) (m : gmap K A) :
  (∀ x k, IntoLater (Φ k x) (Ψ k x)) →
  IntoLater ([★ map] k ↦ x ∈ m, Φ k x) ([★ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLater=> ?. rewrite big_sepM_later; by apply big_sepM_mono.
Qed.
Global Instance into_later_big_sepS `{Countable A}
    (Φ Ψ : A → uPred M) (X : gset A) :
  (∀ x, IntoLater (Φ x) (Ψ x)) →
  IntoLater ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLater=> ?. rewrite big_sepS_later; by apply big_sepS_mono.
Qed.

Global Instance from_later_later P : FromLater (▷ P) P.
Proof. done. Qed.
Global Instance from_later_and P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite later_and; apply and_mono. Qed.
Global Instance from_later_or P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite later_or; apply or_mono. Qed.
Global Instance from_later_sep P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ★ P2) (Q1 ★ Q2).
Proof. intros ??; red. by rewrite later_sep; apply sep_mono. Qed.

Global Instance into_later_env_nil : IntoLaterEnv Enil Enil.
Proof. constructor. Qed.
Global Instance into_later_env_snoc Γ1 Γ2 i P Q :
  IntoLaterEnv Γ1 Γ2 → IntoLater P Q →
  IntoLaterEnv (Esnoc Γ1 i P) (Esnoc Γ2 i Q).
Proof. by constructor. Qed.

Global Instance into_later_envs Γp1 Γp2 Γs1 Γs2 :
  IntoLaterEnv Γp1 Γp2 → IntoLaterEnv Γs1 Γs2 →
  IntoLaterEnvs (Envs Γp1 Γs1) (Envs Γp2 Γs2).
Proof. by split. Qed.

Lemma into_later_env_sound Δ1 Δ2 : IntoLaterEnvs Δ1 Δ2 → Δ1 ⊢ ▷ Δ2.
Proof.
  intros [Hp Hs]; rewrite /of_envs /= !later_sep -always_later.
  repeat apply sep_mono; try apply always_mono.
  - rewrite -later_intro; apply pure_mono; destruct 1; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - induction Hp; rewrite /= ?later_and; auto using and_mono, later_intro.
  - induction Hs; rewrite /= ?later_sep; auto using sep_mono, later_intro.
Qed.

Lemma tac_next Δ Δ' Q Q' :
  IntoLaterEnvs Δ Δ' → FromLater Q Q' → (Δ' ⊢ Q') → Δ ⊢ Q.
Proof. intros ?? HQ. by rewrite -(from_later Q) into_later_env_sound HQ. Qed.

Lemma tac_löb Δ Δ' i Q :
  envs_persistent Δ = true →
  envs_app true (Esnoc Enil i (▷ Q)%I) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite -(always_elim Q) -(löb (□ Q)) -always_later.
  apply impl_intro_l, (always_intro _ _).
  rewrite envs_app_sound //; simpl.
  by rewrite right_id always_and_sep_l' wand_elim_r HQ.
Qed.

(** * Always *)
Lemma tac_always_intro Δ Q : envs_persistent Δ = true → (Δ ⊢ Q) → Δ ⊢ □ Q.
Proof. intros. by apply: always_intro. Qed.

Class IntoPersistentP (P Q : uPred M) := into_persistentP : P ⊢ □ Q.
Arguments into_persistentP : clear implicits.
Global Instance into_persistentP_always_trans P Q :
  IntoPersistentP P Q → IntoPersistentP (□ P) Q | 0.
Proof. rewrite /IntoPersistentP=> ->. by rewrite always_always. Qed.
Global Instance into_persistentP_always P : IntoPersistentP (□ P) P | 1.
Proof. done. Qed.
Global Instance into_persistentP_persistent P :
  PersistentP P → IntoPersistentP P P | 100.
Proof. done. Qed.

Lemma tac_persistent Δ Δ' i p P P' Q :
  envs_lookup i Δ = Some (p, P) → IntoPersistentP P P' →
  envs_replace i p true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_replace_sound //; simpl.
  by rewrite right_id (into_persistentP P) always_if_always wand_elim_r.
Qed.

(** * Implication and wand *)
Lemma tac_impl_intro Δ Δ' i P Q :
  envs_persistent Δ = true →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ?? HQ. rewrite (persistentP Δ) envs_app_sound //; simpl.
  by rewrite right_id always_wand_impl always_elim HQ.
Qed.
Lemma tac_impl_intro_persistent Δ Δ' i P P' Q :
  IntoPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ?? HQ. rewrite envs_app_sound //; simpl. apply impl_intro_l.
  by rewrite right_id {1}(into_persistentP P) always_and_sep_l wand_elim_r.
Qed.
Lemma tac_impl_intro_pure Δ P φ Q : IsPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros. by apply impl_intro_l; rewrite (is_pure P); apply pure_elim_l.
Qed.

Lemma tac_wand_intro Δ Δ' i P Q :
  envs_app false (Esnoc Enil i P) Δ = Some Δ' → (Δ' ⊢ Q) → Δ ⊢ P -★ Q.
Proof.
  intros ? HQ. rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.
Lemma tac_wand_intro_persistent Δ Δ' i P P' Q :
  IntoPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P -★ Q.
Proof.
  intros. rewrite envs_app_sound //; simpl.
  rewrite right_id. by apply wand_mono.
Qed.
Lemma tac_wand_intro_pure Δ P φ Q : IsPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ P -★ Q.
Proof.
  intros. by apply wand_intro_l; rewrite (is_pure P); apply pure_elim_sep_l.
Qed.

Class IntoWand (R P Q : uPred M) := into_wand : R ⊢ P -★ Q.
Arguments into_wand : clear implicits.
Global Instance into_wand_wand P Q : IntoWand (P -★ Q) P Q.
Proof. done. Qed.
Global Instance into_wand_impl P Q : IntoWand (P → Q) P Q.
Proof. apply impl_wand. Qed.
Global Instance into_wand_iff_l P Q : IntoWand (P ↔ Q) P Q.
Proof. by apply and_elim_l', impl_wand. Qed.
Global Instance into_wand_iff_r P Q : IntoWand (P ↔ Q) Q P.
Proof. apply and_elim_r', impl_wand. Qed.
Global Instance into_wand_always R P Q : IntoWand R P Q → IntoWand (□ R) P Q.
Proof. rewrite /IntoWand=> ->. apply always_elim. Qed.

(* This is pretty much [tac_specialize_assert] with [js:=[j]] and [tac_exact],
but it is doing some work to keep the order of hypotheses preserved. *)
Lemma tac_specialize Δ Δ' Δ'' i p j q P1 P2 R Q :
  envs_lookup_delete i Δ = Some (p, P1, Δ') →
  envs_lookup j (if p then Δ else Δ') = Some (q, R) →
  IntoWand R P1 P2 →
  match p with
  | true  => envs_simple_replace j q (Esnoc Enil j P2) Δ
  | false => envs_replace j q false (Esnoc Enil j P2) Δ'
             (* remove [i] and make [j] spatial *)
  end = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_simple_replace_sound //; simpl.
    rewrite assoc (into_wand R) (always_elim_if q) -always_if_sep wand_elim_r.
    by rewrite right_id wand_elim_r.
  - rewrite envs_lookup_sound //; simpl.
    rewrite envs_lookup_sound // (envs_replace_sound' _ Δ'') //; simpl.
    by rewrite right_id assoc (into_wand R) always_if_elim wand_elim_r wand_elim_r.
Qed.

Class IntoAssert (P : uPred M) (Q : uPred M) (R : uPred M) :=
  into_assert : R ★ (P -★ Q) ⊢ Q.
Global Arguments into_assert _ _ _ {_}.
Lemma into_assert_fallthrough P Q : IntoAssert P Q P.
Proof. by rewrite /IntoAssert wand_elim_r. Qed.

Lemma tac_specialize_assert Δ Δ' Δ1 Δ2' j q lr js R P1 P2 P1' Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand R P1 P2 → IntoAssert P1 Q P1' →
  ('(Δ1,Δ2) ← envs_split lr js Δ';
    Δ2' ← envs_app false (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2')) = Some (Δ1,Δ2') → (* does not preserve position of [j] *)
  (Δ1 ⊢ P1') → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 HQ.
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_sound Δ2) //; simpl.
  rewrite right_id (into_wand R) HP1 assoc -(comm _ P1') -assoc.
  rewrite -(into_assert P1 Q); apply sep_mono_r, wand_intro_l.
  by rewrite always_if_elim assoc !wand_elim_r.
Qed.

Lemma tac_specialize_pure Δ Δ' j q R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand R P1 P2 → IsPure P1 φ →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ' →
  φ → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl.
  by rewrite right_id (into_wand R) (is_pure P1) pure_equiv // wand_True wand_elim_r.
Qed.

Lemma tac_specialize_persistent Δ Δ' Δ'' j q P1 P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand R P1 P2 →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ'' →
  (Δ' ⊢ P1) → (PersistentP P1 ∨ PersistentP P2) →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ?? HP1 [?|?] <-.
  - rewrite envs_lookup_sound //.
    rewrite -(idemp uPred_and (envs_delete _ _ _)).
    rewrite {1}HP1 (persistentP P1) always_and_sep_l assoc.
    rewrite envs_simple_replace_sound' //; simpl.
    rewrite right_id (into_wand R) (always_elim_if q) -always_if_sep wand_elim_l.
    by rewrite wand_elim_r.
  - rewrite -(idemp uPred_and Δ) {1}envs_lookup_sound //; simpl; rewrite HP1.
    rewrite envs_simple_replace_sound //; simpl.
    rewrite (sep_elim_r _ (_ -★ _)) right_id (into_wand R) always_if_elim.
    by rewrite wand_elim_l always_and_sep_l -{1}(always_if_always q P2) wand_elim_r.
Qed.

Lemma tac_revert Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  (Δ' ⊢ if p then □ P → Q else P -★ Q) → Δ ⊢ Q.
Proof.
  intros ? HQ. rewrite envs_lookup_delete_sound //; simpl. destruct p.
  - by rewrite HQ -always_and_sep_l impl_elim_r.
  - by rewrite HQ wand_elim_r.
Qed.

Lemma tac_revert_spatial Δ Q :
  (envs_clear_spatial Δ ⊢ env_fold uPred_wand Q (env_spatial Δ)) → Δ ⊢ Q.
Proof.
  intros HΔ. by rewrite envs_clear_spatial_sound HΔ env_fold_wand wand_elim_l.
Qed.

Lemma tac_assert Δ Δ1 Δ2 Δ2' lr js j P Q R :
  IntoAssert P Q R →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ2 = Some Δ2' →
  (Δ1 ⊢ R) → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? HP HQ. rewrite envs_split_sound //.
  rewrite (envs_app_sound Δ2) //; simpl.
  by rewrite right_id HP HQ.
Qed.

Lemma tac_assert_persistent Δ Δ' j P Q :
  envs_app true (Esnoc Enil j P) Δ = Some Δ' →
  (Δ ⊢ P) → PersistentP P → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ? HP ??.
  rewrite -(idemp uPred_and Δ) {1}HP envs_app_sound //; simpl.
  by rewrite right_id {1}(persistentP P) always_and_sep_l wand_elim_r.
Qed.

(** Whenever posing [lem : True ⊢ Q] as [H] we want it to appear as [H : Q] and
not as [H : True -★ Q]. The class [IntoPosedProof] is used to strip off the
[True]. Note that [to_posed_proof_True] is declared using a [Hint Extern] to
make sure it is not used while posing [lem : ?P ⊢ Q] with [?P] an evar. *)
Class IntoPosedProof (P1 P2 R : uPred M) :=
  into_pose_proof : (P1 ⊢ P2) → True ⊢ R.
Arguments into_pose_proof : clear implicits.
Instance to_posed_proof_True P : IntoPosedProof True P P.
Proof. by rewrite /IntoPosedProof. Qed.
Global Instance to_posed_proof_wand P Q : IntoPosedProof P Q (P -★ Q).
Proof. rewrite /IntoPosedProof. apply entails_wand. Qed.

Lemma tac_pose_proof Δ Δ' j P1 P2 R Q :
  (P1 ⊢ P2) → IntoPosedProof P1 P2 R →
  envs_app true (Esnoc Enil j R) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros HP ?? <-. rewrite envs_app_sound //; simpl.
  by rewrite right_id -(into_pose_proof P1 P2 R) // always_pure wand_True.
Qed.

Lemma tac_pose_proof_hyp Δ Δ' Δ'' i p j P Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  envs_app p (Esnoc Enil j P) (if p then Δ else Δ') = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
  - rewrite envs_lookup_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
Qed.

Lemma tac_apply Δ Δ' i p R P1 P2 :
  envs_lookup_delete i Δ = Some (p, R, Δ') → IntoWand R P1 P2 →
  (Δ' ⊢ P1) → Δ ⊢ P2.
Proof.
  intros ?? HP1. rewrite envs_lookup_delete_sound' //.
  by rewrite (into_wand R) HP1 wand_elim_l.
Qed.

(** * Rewriting *)
Lemma tac_rewrite Δ i p Pxy (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : cofeT} (x y : A) (Φ : A → uPred M),
    (Pxy ⊢ x ≡ y) →
    (Q ⊣⊢ Φ (if lr then y else x)) →
    (∀ n, Proper (dist n ==> dist n) Φ) →
    (Δ ⊢ Φ (if lr then x else y)) → Δ ⊢ Q.
Proof.
  intros ? A x y ? HPxy -> ?; apply eq_rewrite; auto.
  rewrite {1}envs_lookup_sound' //; rewrite sep_elim_l HPxy.
  destruct lr; auto using eq_sym.
Qed.

Lemma tac_rewrite_in Δ i p Pxy j q P (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P) →
  ∀ {A : cofeT} Δ' x y (Φ : A → uPred M),
    (Pxy ⊢ x ≡ y) →
    (P ⊣⊢ Φ (if lr then y else x)) →
    (∀ n, Proper (dist n ==> dist n) Φ) →
    envs_simple_replace j q (Esnoc Enil j (Φ (if lr then x else y))) Δ = Some Δ' →
    (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? A Δ' x y Φ HPxy HP ?? <-.
  rewrite -(idemp uPred_and Δ) {2}(envs_lookup_sound' _ i) //.
  rewrite sep_elim_l HPxy always_and_sep_r.
  rewrite (envs_simple_replace_sound _ _ j) //; simpl.
  rewrite HP right_id -assoc; apply wand_elim_r'. destruct lr.
  - apply (eq_rewrite x y (λ y, □?q Φ y -★ Δ')%I); eauto with I. solve_proper.
  - apply (eq_rewrite y x (λ y, □?q Φ y -★ Δ')%I); eauto using eq_sym with I.
    solve_proper.
Qed.

(** * Conjunction splitting *)
Class FromAnd (P Q1 Q2 : uPred M) := from_and : Q1 ∧ Q2 ⊢ P.
Arguments from_and : clear implicits.

Global Instance from_and_and P1 P2 : FromAnd (P1 ∧ P2) P1 P2.
Proof. done. Qed.
Global Instance from_and_sep_persistent_l P1 P2 :
  PersistentP P1 → FromAnd (P1 ★ P2) P1 P2.
Proof. intros. by rewrite /FromAnd always_and_sep_l. Qed.
Global Instance from_and_sep_persistent_r P1 P2 :
  PersistentP P2 → FromAnd (P1 ★ P2) P1 P2.
Proof. intros. by rewrite /FromAnd always_and_sep_r. Qed.
Global Instance from_and_always P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite always_and. Qed.
Global Instance from_and_later P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite later_and. Qed.

Lemma tac_and_split Δ P Q1 Q2 : FromAnd P Q1 Q2 → (Δ ⊢ Q1) → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_and P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Class FromSep (P Q1 Q2 : uPred M) := from_sep : Q1 ★ Q2 ⊢ P.
Arguments from_sep : clear implicits.

Global Instance from_sep_sep P1 P2 : FromSep (P1 ★ P2) P1 P2 | 100.
Proof. done. Qed.
Global Instance from_sep_always P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromSep=> <-. by rewrite always_sep. Qed.
Global Instance from_sep_later P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromSep=> <-. by rewrite later_sep. Qed.

Global Instance from_sep_ownM (a b : M) :
  FromSep (uPred_ownM (a ⋅ b)) (uPred_ownM a) (uPred_ownM b) | 99.
Proof. by rewrite /FromSep ownM_op. Qed.
Global Instance from_sep_big_sepM
    `{Countable K} {A} (Φ Ψ1 Ψ2 : K → A → uPred M) m :
  (∀ k x, FromSep (Φ k x) (Ψ1 k x) (Ψ2 k x)) →
  FromSep ([★ map] k ↦ x ∈ m, Φ k x)
    ([★ map] k ↦ x ∈ m, Ψ1 k x) ([★ map] k ↦ x ∈ m, Ψ2 k x).
Proof.
  rewrite /FromSep=> ?. rewrite -big_sepM_sepM. by apply big_sepM_mono.
Qed.
Global Instance from_sep_big_sepS `{Countable A} (Φ Ψ1 Ψ2 : A → uPred M) X :
  (∀ x, FromSep (Φ x) (Ψ1 x) (Ψ2 x)) →
  FromSep ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ1 x) ([★ set] x ∈ X, Ψ2 x).
Proof.
  rewrite /FromSep=> ?. rewrite -big_sepS_sepS. by apply big_sepS_mono.
Qed.

Lemma tac_sep_split Δ Δ1 Δ2 lr js P Q1 Q2 :
  FromSep P Q1 Q2 →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  (Δ1 ⊢ Q1) → (Δ2 ⊢ Q2) → Δ ⊢ P.
Proof.
  intros. rewrite envs_split_sound // -(from_sep P). by apply sep_mono.
Qed.

(** * Combining *)
Lemma tac_combine Δ1 Δ2 Δ3 Δ4 i1 p P1 i2 q P2 j P Q :
  envs_lookup_delete i1 Δ1 = Some (p,P1,Δ2) →
  envs_lookup_delete i2 (if p then Δ1 else Δ2) = Some (q,P2,Δ3) →
  FromSep P P1 P2 →
  envs_app (p && q) (Esnoc Enil j P)
    (if q then (if p then Δ1 else Δ2) else Δ3) = Some Δ4 →
  (Δ4 ⊢ Q) → Δ1 ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some [? ->]%envs_lookup_delete_Some ?? <-.
  destruct p.
  - rewrite envs_lookup_persistent_sound //. destruct q.
    + rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc -always_sep (from_sep P) wand_elim_r.
    + rewrite envs_lookup_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc always_elim (from_sep P) wand_elim_r.
  - rewrite envs_lookup_sound //; simpl. destruct q.
    + rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc always_elim (from_sep P) wand_elim_r.
    + rewrite envs_lookup_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc (from_sep P) wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Class IntoSep (p: bool) (P Q1 Q2 : uPred M) := into_sep : □?p P ⊢ □?p (Q1 ★ Q2).
Arguments into_sep : clear implicits.
Class IntoOp {A : cmraT} (a b1 b2 : A) := into_op : a ≡ b1 ⋅ b2.
Arguments into_op {_} _ _ _ {_}.

Global Instance into_op_op {A : cmraT} (a b : A) : IntoOp (a ⋅ b) a b.
Proof. by rewrite /IntoOp. Qed.
Global Instance into_op_persistent {A : cmraT} (a : A) :
  Persistent a → IntoOp a a a.
Proof. intros; apply (persistent_dup a). Qed.
Global Instance into_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  IntoOp a b1 b2 → IntoOp a' b1' b2' →
  IntoOp (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance into_op_Some {A : cmraT} (a : A) b1 b2 :
  IntoOp a b1 b2 → IntoOp (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.

Global Instance into_sep_sep p P Q : IntoSep p (P ★ Q) P Q.
Proof. rewrite /IntoSep. by rewrite always_if_sep. Qed.
Global Instance into_sep_ownM p (a b1 b2 : M) :
  IntoOp a b1 b2 →
  IntoSep p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  rewrite /IntoOp /IntoSep=> ->. by rewrite ownM_op always_if_sep.
Qed.

Global Instance into_sep_and P Q : IntoSep true (P ∧ Q) P Q.
Proof. by rewrite /IntoSep /= always_and_sep. Qed.
Global Instance into_sep_and_persistent_l P Q :
  PersistentP P → IntoSep false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoSep /= always_and_sep_l. Qed.
Global Instance into_sep_and_persistent_r P Q :
  PersistentP Q → IntoSep false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoSep /= always_and_sep_r. Qed.

Global Instance into_sep_later p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (▷ P) (▷ Q1) (▷ Q2).
Proof. by rewrite /IntoSep -later_sep !always_if_later=> ->. Qed.

Global Instance into_sep_big_sepM
    `{Countable K} {A} (Φ Ψ1 Ψ2 : K → A → uPred M) p m :
  (∀ k x, IntoSep p (Φ k x) (Ψ1 k x) (Ψ2 k x)) →
  IntoSep p ([★ map] k ↦ x ∈ m, Φ k x)
    ([★ map] k ↦ x ∈ m, Ψ1 k x) ([★ map] k ↦ x ∈ m, Ψ2 k x).
Proof.
  rewrite /IntoSep=> ?. rewrite -big_sepM_sepM !big_sepM_always_if.
  by apply big_sepM_mono.
Qed.
Global Instance into_sep_big_sepS `{Countable A} (Φ Ψ1 Ψ2 : A → uPred M) p X :
  (∀ x, IntoSep p (Φ x) (Ψ1 x) (Ψ2 x)) →
  IntoSep p ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ1 x) ([★ set] x ∈ X, Ψ2 x).
Proof.
  rewrite /IntoSep=> ?. rewrite -big_sepS_sepS !big_sepS_always_if.
  by apply big_sepS_mono.
Qed.

Lemma tac_sep_destruct Δ Δ' i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoSep p P P1 P2 →
  envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl.
  by rewrite (into_sep p P) right_id (comm uPred_sep P1) wand_elim_r.
Qed.

(** * Framing *)
Class Frame (R P Q : uPred M) := frame : R ★ Q ⊢ P.
Arguments frame : clear implicits.

Global Instance frame_here R : Frame R R True.
Proof. by rewrite /Frame right_id. Qed.

Class MakeSep (P Q PQ : uPred M) := make_sep : P ★ Q ⊣⊢ PQ.
Global Instance make_sep_true_l P : MakeSep True P P.
Proof. by rewrite /MakeSep left_id. Qed.
Global Instance make_sep_true_r P : MakeSep P True P.
Proof. by rewrite /MakeSep right_id. Qed.
Global Instance make_sep_fallthrough P Q : MakeSep P Q (P ★ Q) | 100.
Proof. done. Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame R P1 Q → MakeSep Q P2 Q' → Frame R (P1 ★ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r R P1 P2 Q Q' :
  Frame R P2 Q → MakeSep P1 Q Q' → Frame R (P1 ★ P2) Q' | 10.
Proof. rewrite /Frame /MakeSep => <- <-. solve_sep_entails. Qed.

Class MakeAnd (P Q PQ : uPred M) := make_and : P ∧ Q ⊣⊢ PQ.
Global Instance make_and_true_l P : MakeAnd True P P.
Proof. by rewrite /MakeAnd left_id. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. by rewrite /MakeAnd right_id. Qed.
Global Instance make_and_fallthrough P Q : MakeSep P Q (P ★ Q) | 100.
Proof. done. Qed.
Global Instance frame_and_l R P1 P2 Q Q' :
  Frame R P1 Q → MakeAnd Q P2 Q' → Frame R (P1 ∧ P2) Q' | 9.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.
Global Instance frame_and_r R P1 P2 Q Q' :
  Frame R P2 Q → MakeAnd P1 Q Q' → Frame R (P1 ∧ P2) Q' | 10.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.

Class MakeOr (P Q PQ : uPred M) := make_or : P ∨ Q ⊣⊢ PQ.
Global Instance make_or_true_l P : MakeOr True P True.
Proof. by rewrite /MakeOr left_absorb. Qed.
Global Instance make_or_true_r P : MakeOr P True True.
Proof. by rewrite /MakeOr right_absorb. Qed.
Global Instance make_or_fallthrough P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. done. Qed.
Global Instance frame_or R P1 P2 Q1 Q2 Q :
  Frame R P1 Q1 → Frame R P2 Q2 → MakeOr Q1 Q2 Q → Frame R (P1 ∨ P2) Q.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.

Class MakeLater (P lP : uPred M) := make_later : ▷ P ⊣⊢ lP.
Global Instance make_later_true : MakeLater True True.
Proof. by rewrite /MakeLater later_True. Qed.
Global Instance make_later_fallthrough P : MakeLater P (▷ P) | 100.
Proof. done. Qed.

Global Instance frame_later R P Q Q' :
  Frame R P Q → MakeLater Q Q' → Frame R (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLater=><- <-. by rewrite later_sep -(later_intro R).
Qed.

Global Instance frame_exist {A} R (Φ Ψ : A → uPred M) :
  (∀ a, Frame R (Φ a) (Ψ a)) → Frame R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} R (Φ Ψ : A → uPred M) :
  (∀ a, Frame R (Φ a) (Ψ a)) → Frame R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.

Lemma tac_frame Δ Δ' i p R P Q :
  envs_lookup_delete i Δ = Some (p, R, Δ') → Frame R P Q →
  ((if p then Δ else Δ') ⊢ Q) → Δ ⊢ P.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? HQ. destruct p.
  - by rewrite envs_lookup_persistent_sound // always_elim -(frame R P) HQ.
  - rewrite envs_lookup_sound //; simpl. by rewrite -(frame R P) HQ.
Qed.

(** * Disjunction *)
Class FromOr (P Q1 Q2 : uPred M) := from_or : Q1 ∨ Q2 ⊢ P.
Arguments from_or : clear implicits.
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. done. Qed.

Lemma tac_or_l Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q1) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_l'. Qed.
Lemma tac_or_r Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_r'. Qed.

Class IntoOr P Q1 Q2 := into_or : P ⊢ Q1 ∨ Q2.
Arguments into_or : clear implicits.
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. done. Qed.
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.

Lemma tac_or_destruct Δ Δ1 Δ2 i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j1 P1) Δ = Some Δ1 →
  envs_simple_replace i p (Esnoc Enil j2 P2) Δ = Some Δ2 →
  (Δ1 ⊢ Q) → (Δ2 ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? HP1 HP2. rewrite envs_lookup_sound //.
  rewrite (into_or P) always_if_or sep_or_r; apply or_elim.
  - rewrite (envs_simple_replace_sound' _ Δ1) //.
    by rewrite /= right_id wand_elim_r.
  - rewrite (envs_simple_replace_sound' _ Δ2) //.
    by rewrite /= right_id wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → uPred M) : (∀ a, Δ ⊢ Φ a) → Δ ⊢ ∀ a, Φ a.
Proof. apply forall_intro. Qed.

Class ForallSpecialize {As} (xs : hlist As)
  (P : uPred M) (Φ : himpl As (uPred M)) := forall_specialize : P ⊢ Φ xs.
Arguments forall_specialize {_} _ _ _ {_}.

Global Instance forall_specialize_nil P : ForallSpecialize hnil P P | 100.
Proof. done. Qed.
Global Instance forall_specialize_cons A As x xs Φ (Ψ : A → himpl As (uPred M)) :
  (∀ x, ForallSpecialize xs (Φ x) (Ψ x)) →
  ForallSpecialize (hcons x xs) (∀ x : A, Φ x) Ψ.
Proof. rewrite /ForallSpecialize /= => <-. by rewrite (forall_elim x). Qed.

Lemma tac_forall_specialize {As} Δ Δ' i p P (Φ : himpl As (uPred M)) Q xs :
  envs_lookup i Δ = Some (p, P) → ForallSpecialize xs P Φ →
  envs_simple_replace i p (Esnoc Enil i (Φ xs)) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl.
  by rewrite right_id (forall_specialize _ P) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → uPred M) :
  (Δ ⊢ ∀ a, Φ a) → ∀ a, Δ ⊢ Φ a.
Proof. intros HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Class FromExist {A} (P : uPred M) (Φ : A → uPred M) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Arguments from_exist {_} _ _ {_}.
Global Instance from_exist_exist {A} (Φ: A → uPred M): FromExist (∃ a, Φ a) Φ.
Proof. done. Qed.

Lemma tac_exist {A} Δ P (Φ : A → uPred M) :
  FromExist P Φ → (∃ a, Δ ⊢ Φ a) → Δ ⊢ P.
Proof. intros ? [a ?]. rewrite -(from_exist P). eauto using exist_intro'. Qed.

Class IntoExist {A} (P : uPred M) (Φ : A → uPred M) :=
  into_exist : P ⊢ ∃ x, Φ x.
Arguments into_exist {_} _ _ {_}.
Global Instance into_exist_exist {A} (Φ : A → uPred M) : IntoExist (∃ a, Φ a) Φ.
Proof. done. Qed.
Global Instance into_exist_later {A} P (Φ : A → uPred M) :
  IntoExist P Φ → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_always {A} P (Φ : A → uPred M) :
  IntoExist P Φ → IntoExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP always_exist. Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → uPred M) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ →
  (∀ a, ∃ Δ',
    envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ = Some Δ' ∧ (Δ' ⊢ Q)) →
  Δ ⊢ Q.
Proof.
  intros ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) always_if_exist sep_exist_r.
  apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
  rewrite envs_simple_replace_sound' //; simpl. by rewrite right_id wand_elim_r.
Qed.
End tactics.

Hint Extern 0 (IntoPosedProof True _ _) =>
  class_apply @to_posed_proof_True : typeclass_instances.
