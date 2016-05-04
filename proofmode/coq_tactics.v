From iris.algebra Require Export upred.
From iris.algebra Require Import upred_big_op upred_tactics.
From iris.proofmode Require Export environments.
From iris.prelude Require Import stringmap hlist.
Import uPred.

Local Notation "Γ !! j" := (env_lookup j Γ).
Local Notation "x ← y ; z" := (match y with Some x => z | None => None end).
Local Notation "' ( x1 , x2 ) ← y ; z" :=
  (match y with Some (x1,x2) => z | None => None end).
Local Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (match y with Some (x1,x2,x3) => z | None => None end).

Record envs (M : cmraT) :=
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
  (■ envs_wf Δ ★ □ Π∧ env_persistent Δ ★ Π★ env_spatial Δ)%I.

Instance envs_dom {M} : Dom (envs M) stringset := λ Δ,
  dom stringset (env_persistent Δ) ∪ dom stringset (env_spatial Δ).

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

(* if [lr = false] then [result = (hyps named js,remainding hyps)],
   if [lr = true] then [result = (remainding hyps,hyps named js)] *)
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
Context {M : cmraT}.
Implicit Types Γ : env (uPred M).
Implicit Types Δ : envs M.
Implicit Types P Q : uPred M.

Lemma of_envs_def Δ :
  of_envs Δ = (■ envs_wf Δ ★ □ Π∧ env_persistent Δ ★ Π★ env_spatial Δ)%I.
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
  Δ ⊢ ((if p then □ P else P) ★ envs_delete i p Δ).
Proof.
  rewrite /envs_lookup /envs_delete /of_envs=>?; apply const_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_and_sep always_sep.
    ecancel [□ Π∧ _; □ P; Π★ _]%I; apply const_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=.
    ecancel [□ Π∧ _; P; Π★ _]%I; apply const_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
Qed.
Lemma envs_lookup_sound' Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ (P ★ envs_delete i p Δ).
Proof.
  intros. rewrite envs_lookup_sound //. by destruct p; rewrite ?always_elim.
Qed.
Lemma envs_lookup_persistent_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → Δ ⊢ (□ P ★ Δ).
Proof.
  intros. apply: always_entails_l. by rewrite envs_lookup_sound // sep_elim_l.
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) →
  Δ ⊢ ((if p then □ P else P) ★ ((if p then □ P else P) -★ Δ)).
Proof.
  rewrite /envs_lookup /of_envs=>?; apply const_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_and_sep always_sep.
    rewrite const_equiv // left_id.
    cancel [□ P]%I. apply wand_intro_l. solve_sep_entails.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=. rewrite const_equiv // left_id.
    cancel [P]. apply wand_intro_l. solve_sep_entails.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ ((if p then □ P else P) ★ Δ')%I.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound. Qed.
Lemma envs_lookup_delete_sound' Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ (P ★ Δ')%I.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound'. Qed.

Lemma envs_app_sound Δ Δ' p Γ :
  envs_app p Γ Δ = Some Δ' → Δ ⊢ ((if p then □ Π∧ Γ else Π★ Γ) -★ Δ').
Proof.
  rewrite /of_envs /envs_app=> ?; apply const_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply const_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_and_app always_and_sep always_sep; solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply const_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γs') // big_sep_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ ((if p then □ Π∧ Γ else Π★ Γ) -★ Δ')%I.
Proof.
  rewrite /envs_simple_replace /envs_delete /of_envs=> ?.
  apply const_elim_sep_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply const_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_and_app always_and_sep always_sep; solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply const_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_sep_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  Δ ⊢ ((if p then □ P else P) ★
       ((if p then □ Π∧ Γ else Π★ Γ) -★ Δ'))%I.
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ ((if q then □ Π∧ Γ else Π★ Γ) -★ Δ')%I.
Proof.
  rewrite /envs_replace; destruct (eqb _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  Δ ⊢ ((if p then □ P else P) ★
       ((if q then □ Π∧ Γ else Π★ Γ) -★ Δ'))%I.
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_split_sound Δ lr js Δ1 Δ2 :
  envs_split lr js Δ = Some (Δ1,Δ2) → Δ ⊢ (Δ1 ★ Δ2).
Proof.
  rewrite /envs_split /of_envs=> ?; apply const_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (env_split js _) as [[Γs1 Γs2]|] eqn:?; simplify_eq/=.
  rewrite (env_split_perm Γs) // big_sep_app {1}always_sep_dup'.
  destruct lr; simplify_eq/=; cancel [□ Π∧ Γp; □ Π∧ Γp; Π★ Γs1; Π★ Γs2]%I;
    destruct Hwf; apply sep_intro_True_l; apply const_intro; constructor;
      naive_solver eauto using env_split_wf_1, env_split_wf_2,
      env_split_fresh_1, env_split_fresh_2.
Qed.

Lemma envs_clear_spatial_sound Δ :
  Δ ⊢ (envs_clear_spatial Δ ★ Π★ env_spatial Δ)%I.
Proof.
  rewrite /of_envs /envs_clear_spatial /=; apply const_elim_sep_l=> Hwf.
  rewrite right_id -assoc; apply sep_intro_True_l; [apply const_intro|done].
  destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_fold_wand Γ Q : env_fold uPred_wand Q Γ ⊣⊢ (Π★ Γ -★ Q).
Proof.
  revert Q; induction Γ as [|Γ IH i P]=> Q /=; [by rewrite wand_True|].
  by rewrite IH wand_curry (comm uPred_sep).
Qed.

Lemma envs_persistent_persistent Δ : envs_persistent Δ = true → PersistentP Δ.
Proof. intros; destruct Δ as [? []]; simplify_eq/=; apply _. Qed.
Hint Immediate envs_persistent_persistent : typeclass_instances.

(** * Adequacy *)
Lemma tac_adequate P : Envs Enil Enil ⊢ P → True ⊢ P.
Proof.
  intros <-. rewrite /of_envs /= always_const !right_id.
  apply const_intro; repeat constructor.
Qed.

(** * Basic rules *)
Class ToAssumption (p : bool) (P Q : uPred M) :=
  to_assumption : (if p then □ P else P) ⊢ Q.
Global Instance to_assumption_exact p P : ToAssumption p P P.
Proof. destruct p; by rewrite /ToAssumption ?always_elim. Qed.
Global Instance to_assumption_always P Q :
  ToAssumption true P Q → ToAssumption true P (□ Q).
Proof. rewrite /ToAssumption=><-. by rewrite always_always. Qed.

Lemma tac_assumption Δ i p P Q :
  envs_lookup i Δ = Some (p,P) → ToAssumption p P Q → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_sound // sep_elim_l. Qed.

Lemma tac_rename Δ Δ' i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j P) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //.
  destruct p; simpl; by rewrite right_id wand_elim_r.
Qed.
Lemma tac_clear Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ' ⊢ Q → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_delete_sound // sep_elim_r. Qed.
Lemma tac_clear_spatial Δ Δ' Q :
  envs_clear_spatial Δ = Δ' → Δ' ⊢ Q → Δ ⊢ Q.
Proof. intros <- ?. by rewrite envs_clear_spatial_sound // sep_elim_l. Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : Δ ⊢ False → Δ ⊢ Q.
Proof. by rewrite -(False_elim Q). Qed.

(** * Pure *)
Class ToPure (P : uPred M) (φ : Prop) := to_pure : P ⊣⊢ ■ φ.
Arguments to_pure : clear implicits.
Global Instance to_pure_const φ : ToPure (■ φ) φ.
Proof. done. Qed.
Global Instance to_pure_eq {A : cofeT} (a b : A) :
  Timeless a → ToPure (a ≡ b) (a ≡ b).
Proof. intros; red. by rewrite timeless_eq. Qed.
Global Instance to_pure_valid `{CMRADiscrete A} (a : A) : ToPure (✓ a) (✓ a).
Proof. intros; red. by rewrite discrete_valid. Qed.

Lemma tac_pure_intro Δ Q (φ : Prop) : ToPure Q φ → φ → Δ ⊢ Q.
Proof. intros ->. apply const_intro. Qed.

Lemma tac_pure Δ Δ' i p P φ Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') → ToPure P φ →
  (φ → Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite envs_lookup_delete_sound' //; simpl.
  rewrite (to_pure P); by apply const_elim_sep_l.
Qed.

Lemma tac_pure_revert Δ φ Q : Δ ⊢ (■ φ → Q) → (φ → Δ ⊢ Q).
Proof. intros HΔ ?. by rewrite HΔ const_equiv // left_id. Qed.

(** * Later *)
Class StripLaterEnv (Γ1 Γ2 : env (uPred M)) :=
  strip_later_env : env_Forall2 StripLaterR Γ1 Γ2.
Global Instance strip_later_env_nil : StripLaterEnv Enil Enil.
Proof. constructor. Qed.
Global Instance strip_later_env_snoc Γ1 Γ2 i P Q :
  StripLaterEnv Γ1 Γ2 → StripLaterR P Q →
  StripLaterEnv (Esnoc Γ1 i P) (Esnoc Γ2 i Q).
Proof. by constructor. Qed.

Class StripLaterEnvs (Δ1 Δ2 : envs M) := {
  strip_later_persistent: StripLaterEnv (env_persistent Δ1) (env_persistent Δ2);
  strip_later_spatial: StripLaterEnv (env_spatial Δ1) (env_spatial Δ2)
}.
Global Instance strip_later_envs Γp1 Γp2 Γs1 Γs2 :
  StripLaterEnv Γp1 Γp2 → StripLaterEnv Γs1 Γs2 →
  StripLaterEnvs (Envs Γp1 Γs1) (Envs Γp2 Γs2).
Proof. by split. Qed.
Lemma strip_later_env_sound Δ1 Δ2 : StripLaterEnvs Δ1 Δ2 → Δ1 ⊢ ▷ Δ2.
Proof.
  intros [Hp Hs]; rewrite /of_envs /= !later_sep -always_later.
  repeat apply sep_mono; try apply always_mono.
  - rewrite -later_intro; apply const_mono; destruct 1; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - induction Hp; rewrite /= ?later_and; auto using and_mono, later_intro.
  - induction Hs; rewrite /= ?later_sep; auto using sep_mono, later_intro.
Qed.

Lemma tac_next Δ Δ' Q Q' :
  StripLaterEnvs Δ Δ' → StripLaterL Q Q' → Δ' ⊢ Q' → Δ ⊢ Q.
Proof. intros ?? HQ. by rewrite -(strip_later_l Q) strip_later_env_sound HQ. Qed.

Lemma tac_löb Δ Δ' i Q :
  envs_persistent Δ = true →
  envs_app true (Esnoc Enil i (▷ Q)%I) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite -(always_elim Q) -(löb (□ Q)) -always_later.
  apply impl_intro_l, (always_intro _ _).
  rewrite envs_app_sound //; simpl.
  by rewrite right_id always_and_sep_l' wand_elim_r HQ.
Qed.

(** * Always *)
Lemma tac_always_intro Δ Q : envs_persistent Δ = true → Δ ⊢ Q → Δ ⊢ □ Q.
Proof. intros. by apply: always_intro. Qed.

Class ToPersistentP (P Q : uPred M) := to_persistentP : P ⊢ □ Q.
Arguments to_persistentP : clear implicits.
Global Instance to_persistentP_always_trans P Q :
  ToPersistentP P Q → ToPersistentP (□ P) Q | 0.
Proof. rewrite /ToPersistentP=> ->. by rewrite always_always. Qed.
Global Instance to_persistentP_always P : ToPersistentP (□ P) P | 1.
Proof. done. Qed.
Global Instance to_persistentP_persistent P :
  PersistentP P → ToPersistentP P P | 100.
Proof. done. Qed.

Lemma tac_persistent Δ Δ' i p P P' Q :
  envs_lookup i Δ = Some (p, P)%I → ToPersistentP P P' →
  envs_replace i p true (Esnoc Enil i P') Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_replace_sound //; simpl. destruct p.
  - by rewrite right_id (to_persistentP P) always_always wand_elim_r.
  - by rewrite right_id (to_persistentP P) wand_elim_r.
Qed.

(** * Implication and wand *)
Lemma tac_impl_intro Δ Δ' i P Q :
  envs_persistent Δ = true →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ (P → Q).
Proof.
  intros ?? HQ. rewrite (persistentP Δ) envs_app_sound //; simpl.
  by rewrite right_id always_wand_impl always_elim HQ.
Qed.
Lemma tac_impl_intro_persistent Δ Δ' i P P' Q :
  ToPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ (P → Q).
Proof.
  intros ?? HQ. rewrite envs_app_sound //; simpl. apply impl_intro_l.
  by rewrite right_id {1}(to_persistentP P) always_and_sep_l wand_elim_r.
Qed.
Lemma tac_impl_intro_pure Δ P φ Q : ToPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ (P → Q).
Proof.
  intros. by apply impl_intro_l; rewrite (to_pure P); apply const_elim_l.
Qed.

Lemma tac_wand_intro Δ Δ' i P Q :
  envs_app false (Esnoc Enil i P) Δ = Some Δ' → Δ' ⊢ Q → Δ ⊢ (P -★ Q).
Proof.
  intros. rewrite envs_app_sound //; simpl.
  rewrite right_id. by apply wand_mono.
Qed.
Lemma tac_wand_intro_persistent Δ Δ' i P P' Q :
  ToPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ (P -★ Q).
Proof.
  intros. rewrite envs_app_sound //; simpl.
  rewrite right_id. by apply wand_mono.
Qed.
Lemma tac_wand_intro_pure Δ P φ Q : ToPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ (P -★ Q).
Proof.
  intros. by apply wand_intro_l; rewrite (to_pure P); apply const_elim_sep_l.
Qed.

Class ToWand (R P Q : uPred M) := to_wand : R ⊢ (P -★ Q).
Arguments to_wand : clear implicits.
Global Instance to_wand_wand P Q : ToWand (P -★ Q) P Q.
Proof. done. Qed.
Global Instance to_wand_impl P Q : ToWand (P → Q) P Q.
Proof. apply impl_wand. Qed.
Global Instance to_wand_iff_l P Q : ToWand (P ↔ Q) P Q.
Proof. by apply and_elim_l', impl_wand. Qed.
Global Instance to_wand_iff_r P Q : ToWand (P ↔ Q) Q P.
Proof. apply and_elim_r', impl_wand. Qed.

(* This is pretty much [tac_specialize_assert] with [js:=[j]] and [tac_exact],
but it is doing some work to keep the order of hypotheses preserved. *)
Lemma tac_specialize Δ Δ' Δ'' i p j q P1 P2 R Q :
  envs_lookup_delete i Δ = Some (p, P1, Δ') →
  envs_lookup j (if p then Δ else Δ') = Some (q, R)%I →
  ToWand R P1 P2 →
  match p with
  | true  => envs_simple_replace j q (Esnoc Enil j P2) Δ
  | false => envs_replace j q false (Esnoc Enil j P2) Δ'
             (* remove [i] and make [j] spatial *)
  end = Some Δ'' →
  Δ'' ⊢ Q → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_simple_replace_sound //; simpl.
    destruct q.
    + by rewrite assoc (to_wand R) always_wand wand_elim_r right_id wand_elim_r.
    + by rewrite assoc (to_wand R) always_elim wand_elim_r right_id wand_elim_r.
  - rewrite envs_lookup_sound //; simpl.
    rewrite envs_lookup_sound // (envs_replace_sound' _ Δ'') //; simpl.
    destruct q.
    + by rewrite right_id assoc (to_wand R) always_elim wand_elim_r wand_elim_r.
    + by rewrite assoc (to_wand R) wand_elim_r right_id wand_elim_r.
Qed.

Lemma tac_specialize_assert Δ Δ' Δ1 Δ2' j q lr js P1 P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ')%I →
  ToWand R P1 P2 →
  ('(Δ1,Δ2) ← envs_split lr js Δ';
    Δ2' ← envs_app (envs_persistent Δ1 && q) (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2')) = Some (Δ1,Δ2') → (* does not preserve position of [j] *)
  Δ1 ⊢ P1 → Δ2' ⊢ Q → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ?? HP1 <-.
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_sound Δ2) //; simpl.
  destruct q, (envs_persistent Δ1) eqn:?; simplify_eq/=.
  - rewrite right_id (to_wand R) (persistentP Δ1) HP1.
    by rewrite assoc -always_sep wand_elim_l wand_elim_r.
  - by rewrite right_id (to_wand R) always_elim assoc HP1 wand_elim_l wand_elim_r.
  - by rewrite right_id (to_wand R) assoc HP1 wand_elim_l wand_elim_r.
  - by rewrite right_id (to_wand R) assoc HP1 wand_elim_l wand_elim_r. 
Qed.

Lemma tac_specialize_range_persistent Δ Δ' Δ'' j q P1 P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ')%I →
  ToWand R P1 P2 → PersistentP P1 →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ'' →
  Δ' ⊢ P1 → Δ'' ⊢ Q → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 <-.
  rewrite envs_lookup_sound //.
  rewrite -(idemp uPred_and (envs_delete _ _ _)).
  rewrite {1}HP1 (persistentP P1) always_and_sep_l assoc.
  rewrite envs_simple_replace_sound' //; simpl. destruct q.
  - by rewrite right_id (to_wand R) -always_sep wand_elim_l wand_elim_r.
  - by rewrite right_id (to_wand R) always_elim wand_elim_l wand_elim_r.
Qed.

Lemma tac_specialize_domain_persistent Δ Δ' Δ'' j q P1 P2 P2' R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ')%I →
  ToWand R P1 P2 → ToPersistentP P2 P2' →
  envs_replace j q true (Esnoc Enil j P2') Δ = Some Δ'' →
  Δ' ⊢ P1 → Δ'' ⊢ Q → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 <-.
  rewrite -(idemp uPred_and Δ) {1}envs_lookup_sound //; simpl; rewrite HP1.
  rewrite envs_replace_sound //; simpl.
  rewrite (sep_elim_r _ (_ -★ _)) right_id. destruct q.
  - rewrite (to_wand R) always_elim wand_elim_l.
    by rewrite (to_persistentP P2) always_and_sep_l' wand_elim_r.
  - rewrite (to_wand R) wand_elim_l.
    by rewrite (to_persistentP P2) always_and_sep_l' wand_elim_r.
Qed.

Lemma tac_revert Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  Δ' ⊢ (if p then □ P → Q else P -★ Q) → Δ ⊢ Q.
Proof.
  intros ? HQ. rewrite envs_lookup_delete_sound //; simpl. destruct p.
  - by rewrite HQ -always_and_sep_l impl_elim_r.
  - by rewrite HQ wand_elim_r.
Qed.

Lemma tac_revert_spatial Δ Q :
  envs_clear_spatial Δ ⊢ (env_fold uPred_wand Q (env_spatial Δ)) → Δ ⊢ Q.
Proof.
  intros HΔ. by rewrite envs_clear_spatial_sound HΔ env_fold_wand wand_elim_l.
Qed.

Lemma tac_assert Δ Δ1 Δ2 Δ2' lr js j P Q :
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app (envs_persistent Δ1) (Esnoc Enil j P) Δ2 = Some Δ2' →
  Δ1 ⊢ P → Δ2' ⊢ Q → Δ ⊢ Q.
Proof.
  intros ?? HP ?. rewrite envs_split_sound //.
  destruct (envs_persistent Δ1) eqn:?.
  - rewrite (persistentP Δ1) HP envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
  - rewrite HP envs_app_sound //; simpl. by rewrite right_id wand_elim_r.
Qed.

Lemma tac_assert_persistent Δ Δ' j P Q :
  PersistentP P →
  envs_app true (Esnoc Enil j P) Δ = Some Δ' →
  Δ ⊢ P → Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros ?? HP ?.
  rewrite -(idemp uPred_and Δ) {1}HP envs_app_sound //; simpl.
  by rewrite right_id {1}(persistentP P) always_and_sep_l wand_elim_r.
Qed.

(** Whenever posing [lem : True ⊢ Q] as [H] we want it to appear as [H : Q] and
not as [H : True -★ Q]. The class [ToPosedProof] is used to strip off the
[True]. Note that [to_posed_proof_True] is declared using a [Hint Extern] to
make sure it is not used while posing [lem : ?P ⊢ Q] with [?P] an evar. *)
Class ToPosedProof (P1 P2 R : uPred M) := to_pose_proof : P1 ⊢ P2 → True ⊢ R.
Arguments to_pose_proof : clear implicits.
Instance to_posed_proof_True P : ToPosedProof True P P.
Proof. by rewrite /ToPosedProof. Qed.
Global Instance to_posed_proof_wand P Q : ToPosedProof P Q (P -★ Q).
Proof. rewrite /ToPosedProof. apply entails_wand. Qed.

Lemma tac_pose_proof Δ Δ' j P1 P2 R Q :
  P1 ⊢ P2 → ToPosedProof P1 P2 R → envs_app true (Esnoc Enil j R) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros HP ?? <-. rewrite envs_app_sound //; simpl.
  by rewrite right_id -(to_pose_proof P1 P2 R) // always_const wand_True.
Qed.

Lemma tac_pose_proof_hyp Δ Δ' Δ'' i p j P Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  envs_app p (Esnoc Enil j P) (if p then Δ else Δ') = Some Δ'' →
  Δ'' ⊢ Q → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
  - rewrite envs_lookup_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
Qed.

Lemma tac_apply Δ Δ' i p R P1 P2 :
  envs_lookup_delete i Δ = Some (p, R, Δ')%I → ToWand R P1 P2 →
  Δ' ⊢ P1 → Δ ⊢ P2.
Proof.
  intros ?? HP1. rewrite envs_lookup_delete_sound' //.
  by rewrite (to_wand R) HP1 wand_elim_l.
Qed.

(** * Rewriting *)
Lemma tac_rewrite Δ i p Pxy (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : cofeT} (x y : A) (Φ : A → uPred M),
    Pxy ⊢ (x ≡ y)%I →
    Q ⊣⊢ Φ (if lr then y else x) →
    (∀ n, Proper (dist n ==> dist n) Φ) →
    Δ ⊢ Φ (if lr then x else y) → Δ ⊢ Q.
Proof.
  intros ? A x y ? HPxy -> ?; apply eq_rewrite; auto.
  rewrite {1}envs_lookup_sound' //; rewrite sep_elim_l HPxy.
  destruct lr; auto using eq_sym.
Qed.

Lemma tac_rewrite_in Δ i p Pxy j q P (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P)%I →
  ∀ {A : cofeT} Δ' x y (Φ : A → uPred M),
    Pxy ⊢ (x ≡ y)%I →
    P ⊣⊢ Φ (if lr then y else x) →
    (∀ n, Proper (dist n ==> dist n) Φ) →
    envs_simple_replace j q (Esnoc Enil j (Φ (if lr then x else y))) Δ = Some Δ' →
    Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros ?? A Δ' x y Φ HPxy HP ?? <-.
  rewrite -(idemp uPred_and Δ) {2}(envs_lookup_sound' _ i) //.
  rewrite sep_elim_l HPxy always_and_sep_r.
  rewrite (envs_simple_replace_sound _ _ j) //; simpl. destruct q.
  - rewrite HP right_id -assoc; apply wand_elim_r'. destruct lr.
    + apply (eq_rewrite x y (λ y, □ Φ y -★ Δ')%I); eauto with I. solve_proper.
    + apply (eq_rewrite y x (λ y, □ Φ y -★ Δ')%I); eauto using eq_sym with I.
      solve_proper.
  - rewrite HP right_id -assoc; apply wand_elim_r'. destruct lr.
    + apply (eq_rewrite x y (λ y, Φ y -★ Δ')%I); eauto with I. solve_proper.
    + apply (eq_rewrite y x (λ y, Φ y -★ Δ')%I); eauto using eq_sym with I.
      solve_proper.
Qed.

(** * Conjunction splitting *)
Class AndSplit (P Q1 Q2 : uPred M) := and_split : (Q1 ∧ Q2) ⊢ P.
Arguments and_split : clear implicits.

Global Instance and_split_and P1 P2 : AndSplit (P1 ∧ P2) P1 P2.
Proof. done. Qed.
Global Instance and_split_sep_persistent_l P1 P2 :
  PersistentP P1 → AndSplit (P1 ★ P2) P1 P2.
Proof. intros. by rewrite /AndSplit always_and_sep_l. Qed.
Global Instance and_split_sep_persistent_r P1 P2 :
  PersistentP P2 → AndSplit (P1 ★ P2) P1 P2.
Proof. intros. by rewrite /AndSplit always_and_sep_r. Qed.

Lemma tac_and_split Δ P Q1 Q2 : AndSplit P Q1 Q2 → Δ ⊢ Q1 → Δ ⊢ Q2 → Δ ⊢ P.
Proof. intros. rewrite -(and_split P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Class SepSplit (P Q1 Q2 : uPred M) := sep_split : (Q1 ★ Q2) ⊢ P.
Arguments sep_split : clear implicits.

Global Instance sep_split_sep P1 P2 : SepSplit (P1 ★ P2) P1 P2 | 100.
Proof. done. Qed.
Global Instance sep_split_ownM (a b : M) :
  SepSplit (uPred_ownM (a ⋅ b)) (uPred_ownM a) (uPred_ownM b) | 99.
Proof. by rewrite /SepSplit ownM_op. Qed.

Lemma tac_sep_split Δ Δ1 Δ2 lr js P Q1 Q2 :
  SepSplit P Q1 Q2 →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  Δ1 ⊢ Q1 → Δ2 ⊢ Q2 → Δ ⊢ P.
Proof.
  intros. rewrite envs_split_sound // -(sep_split P). by apply sep_mono.
Qed.

(** * Combining *)
Lemma tac_combine Δ1 Δ2 Δ3 Δ4 i1 p P1 i2 q P2 j P Q :
  envs_lookup_delete i1 Δ1 = Some (p,P1,Δ2) →
  envs_lookup_delete i2 (if p then Δ1 else Δ2) = Some (q,P2,Δ3) →
  SepSplit P P1 P2 →
  envs_app (p && q) (Esnoc Enil j P)
    (if q then (if p then Δ1 else Δ2) else Δ3) = Some Δ4 →
  Δ4 ⊢ Q → Δ1 ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some [? ->]%envs_lookup_delete_Some ?? <-.
  destruct p.
  - rewrite envs_lookup_persistent_sound //. destruct q.
    + rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc -always_sep (sep_split P) wand_elim_r.
    + rewrite envs_lookup_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc always_elim (sep_split P) wand_elim_r.
  - rewrite envs_lookup_sound //; simpl. destruct q.
    + rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc always_elim (sep_split P) wand_elim_r.
    + rewrite envs_lookup_sound // envs_app_sound //; simpl.
      by rewrite right_id assoc (sep_split P) wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Class SepDestruct (p : bool) (P Q1 Q2 : uPred M) :=
  sep_destruct : if p then □ P ⊢ □ (Q1 ∧ Q2) else P ⊢ (Q1 ★ Q2).
Arguments sep_destruct : clear implicits.
Lemma sep_destruct_spatial p P Q1 Q2 : P ⊢ (Q1 ★ Q2) → SepDestruct p P Q1 Q2.
Proof. destruct p; simpl=>->; by rewrite ?sep_and. Qed.

Global Instance sep_destruct_sep p P Q : SepDestruct p (P ★ Q) P Q.
Proof. by apply sep_destruct_spatial. Qed.
Global Instance sep_destruct_ownM p (a b : M) :
  SepDestruct p (uPred_ownM (a ⋅ b)) (uPred_ownM a) (uPred_ownM b).
Proof. apply sep_destruct_spatial. by rewrite ownM_op. Qed.

Global Instance sep_destruct_and P Q : SepDestruct true (P ∧ Q) P Q.
Proof. done. Qed.
Global Instance sep_destruct_and_persistent_l P Q :
  PersistentP P → SepDestruct false (P ∧ Q) P Q.
Proof. intros; red. by rewrite always_and_sep_l. Qed.
Global Instance sep_destruct_and_persistent_r P Q :
  PersistentP Q → SepDestruct false (P ∧ Q) P Q.
Proof. intros; red. by rewrite always_and_sep_r. Qed.

Global Instance sep_destruct_later p P Q1 Q2 :
  SepDestruct p P Q1 Q2 → SepDestruct p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  destruct p=> /= HP.
  - by rewrite -later_and !always_later HP.
  - by rewrite -later_sep HP.
Qed.

Lemma tac_sep_destruct Δ Δ' i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P)%I → SepDestruct p P P1 P2 →
  envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl. destruct p.
  - by rewrite (sep_destruct true P) right_id (comm uPred_and) wand_elim_r.
  - by rewrite (sep_destruct false P) right_id (comm uPred_sep P1) wand_elim_r.
Qed.

(** * Framing *)
(** The [option] is to account for formulas that can be framed entirely, so
we do not end up with [True]s everywhere. *)
Class Frame (R P : uPred M) (mQ : option (uPred M)) :=
  frame : (R ★ from_option True mQ) ⊢ P.
Arguments frame : clear implicits.

Global Instance frame_here R : Frame R R None.
Proof. by rewrite /Frame right_id. Qed.
Global Instance frame_sep_l R P1 P2 mQ :
  Frame R P1 mQ →
  Frame R (P1 ★ P2) (Some $ if mQ is Some Q then Q ★ P2 else P2)%I | 9.
Proof. rewrite /Frame => <-. destruct mQ; simpl; solve_sep_entails. Qed.
Global Instance frame_sep_r R P1 P2 mQ :
  Frame R P2 mQ →
  Frame R (P1 ★ P2) (Some $ if mQ is Some Q then P1 ★ Q else P1)%I | 10.
Proof. rewrite /Frame => <-. destruct mQ; simpl; solve_sep_entails. Qed.
Global Instance frame_and_l R P1 P2 mQ :
  Frame R P1 mQ →
  Frame R (P1 ∧ P2) (Some $ if mQ is Some Q then Q ∧ P2 else P2)%I | 9.
Proof. rewrite /Frame => <-. destruct mQ; simpl; eauto 10 with I. Qed.
Global Instance frame_and_r R P1 P2 mQ :
  Frame R P2 mQ →
  Frame R (P1 ∧ P2) (Some $ if mQ is Some Q then P1 ∧ Q else P1)%I | 10.
Proof. rewrite /Frame => <-. destruct mQ; simpl; eauto 10 with I. Qed.
Global Instance frame_or R P1 P2 mQ1 mQ2 :
  Frame R P1 mQ1 → Frame R P2 mQ2 →
  Frame R (P1 ∨ P2) (match mQ1, mQ2 with
                     | Some Q1, Some Q2 => Some (Q1 ∨ Q2)%I | _, _ => None
                     end).
Proof.
  rewrite /Frame=> <- <-.
  destruct mQ1 as [Q1|], mQ2 as [Q2|]; simpl; auto with I.
  by rewrite -sep_or_l.
Qed.
Global Instance frame_later R P mQ :
  Frame R P mQ → Frame R (▷ P) (if mQ is Some Q then Some (▷ Q) else None)%I.
Proof.
  rewrite /Frame=><-.
  by destruct mQ; rewrite /= later_sep -(later_intro R) ?later_True.
Qed.
Global Instance frame_exist {A} R (Φ : A → uPred M) mΨ :
  (∀ a, Frame R (Φ a) (mΨ a)) →
  Frame R (∃ x, Φ x) (Some (∃ x, if mΨ x is Some Q then Q else True))%I.
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} R (Φ : A → uPred M) mΨ :
  (∀ a, Frame R (Φ a) (mΨ a)) →
  Frame R (∀ x, Φ x) (Some (∀ x, if mΨ x is Some Q then Q else True))%I.
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.

Lemma tac_frame Δ Δ' i p R P mQ :
  envs_lookup_delete i Δ = Some (p, R, Δ')%I → Frame R P mQ →
  (if mQ is Some Q then (if p then Δ else Δ') ⊢ Q else True) →
  Δ ⊢ P.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? HQ. destruct p.
  - rewrite envs_lookup_persistent_sound // always_elim.
    rewrite -(frame R P). destruct mQ as [Q|]; rewrite ?HQ /=; auto with I.
  - rewrite envs_lookup_sound //; simpl.
    rewrite -(frame R P). destruct mQ as [Q|]; rewrite ?HQ /=; auto with I.
Qed.

(** * Disjunction *)
Class OrSplit (P Q1 Q2 : uPred M) := or_split : (Q1 ∨ Q2) ⊢ P.
Arguments or_split : clear implicits.
Global Instance or_split_or P1 P2 : OrSplit (P1 ∨ P2) P1 P2.
Proof. done. Qed.

Lemma tac_or_l Δ P Q1 Q2 : OrSplit P Q1 Q2 → Δ ⊢ Q1 → Δ ⊢ P.
Proof. intros. rewrite -(or_split P). by apply or_intro_l'. Qed.
Lemma tac_or_r Δ P Q1 Q2 : OrSplit P Q1 Q2 → Δ ⊢ Q2 → Δ ⊢ P.
Proof. intros. rewrite -(or_split P). by apply or_intro_r'. Qed.

Class OrDestruct P Q1 Q2 := or_destruct : P ⊢ (Q1 ∨ Q2).
Arguments or_destruct : clear implicits.
Global Instance or_destruct_or P Q : OrDestruct (P ∨ Q) P Q.
Proof. done. Qed.
Global Instance or_destruct_later P Q1 Q2 :
  OrDestruct P Q1 Q2 → OrDestruct (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /OrDestruct=>->. by rewrite later_or. Qed.

Lemma tac_or_destruct Δ Δ1 Δ2 i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → OrDestruct P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j1 P1) Δ = Some Δ1 →
  envs_simple_replace i p (Esnoc Enil j2 P2) Δ = Some Δ2 →
  Δ1 ⊢ Q → Δ2 ⊢ Q → Δ ⊢ Q.
Proof.
  intros ???? HP1 HP2. rewrite envs_lookup_sound //. destruct p.
  - rewrite (or_destruct P) always_or sep_or_r; apply or_elim. simpl.
    + rewrite (envs_simple_replace_sound' _ Δ1) //.
      by rewrite /= right_id wand_elim_r.
    + rewrite (envs_simple_replace_sound' _ Δ2) //.
      by rewrite /= right_id wand_elim_r.
  - rewrite (or_destruct P) sep_or_r; apply or_elim.
    + rewrite (envs_simple_replace_sound' _ Δ1) //.
      by rewrite /= right_id wand_elim_r.
    + rewrite (envs_simple_replace_sound' _ Δ2) //.
      by rewrite /= right_id wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → uPred M) : (∀ a, Δ ⊢ Φ a) → Δ ⊢ (∀ a, Φ a).
Proof. apply forall_intro. Qed.

Class ForallSpecialize {As} (xs : hlist As)
    (P : uPred M) (Φ : himpl As (uPred M)) :=
  forall_specialize : P ⊢ happly Φ xs.
Arguments forall_specialize {_} _ _ _ {_}.

Global Instance forall_specialize_nil P : ForallSpecialize hnil P P | 100.
Proof. done. Qed.
Global Instance forall_specialize_cons A As x xs Φ (Ψ : A → himpl As (uPred M)) :
  (∀ x, ForallSpecialize xs (Φ x) (Ψ x)) →
  ForallSpecialize (hcons x xs) (∀ x : A, Φ x) Ψ.
Proof. rewrite /ForallSpecialize /= => <-. by rewrite (forall_elim x). Qed.

Lemma tac_forall_specialize {As} Δ Δ' i p P (Φ : himpl As (uPred M)) Q xs :
  envs_lookup i Δ = Some (p, P) → ForallSpecialize xs P Φ →
  envs_simple_replace i p (Esnoc Enil i (happly Φ xs)) Δ = Some Δ' →
  Δ' ⊢ Q → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl. destruct p.
  - by rewrite right_id (forall_specialize _ P) wand_elim_r.
  - by rewrite right_id (forall_specialize _ P) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → uPred M) :
  Δ ⊢ (∀ a, Φ a) → (∀ a, Δ ⊢ Φ a).
Proof. intros HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Class ExistSplit {A} (P : uPred M) (Φ : A → uPred M) :=
  exist_split : (∃ x, Φ x) ⊢ P.
Arguments exist_split {_} _ _ {_}.
Global Instance exist_split_exist {A} (Φ: A → uPred M): ExistSplit (∃ a, Φ a) Φ.
Proof. done. Qed.

Lemma tac_exist {A} Δ P (Φ : A → uPred M) :
  ExistSplit P Φ → (∃ a, Δ ⊢ Φ a) → Δ ⊢ P.
Proof. intros ? [a ?]. rewrite -(exist_split P). eauto using exist_intro'. Qed.

Class ExistDestruct {A} (P : uPred M) (Φ : A → uPred M) :=
  exist_destruct : P ⊢ (∃ x, Φ x).
Arguments exist_destruct {_} _ _ {_}.
Global Instance exist_destruct_exist {A} (Φ : A → uPred M) :
  ExistDestruct (∃ a, Φ a) Φ.
Proof. done. Qed.
Global Instance exist_destruct_later {A} P (Φ : A → uPred M) :
  Inhabited A → ExistDestruct P Φ → ExistDestruct (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /ExistDestruct=> ? ->. by rewrite later_exist. Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → uPred M) Q :
  envs_lookup i Δ = Some (p, P)%I → ExistDestruct P Φ →
  (∀ a, ∃ Δ',
    envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ = Some Δ' ∧ Δ' ⊢ Q) →
  Δ ⊢ Q.
Proof.
  intros ?? HΦ. rewrite envs_lookup_sound //. destruct p.
  - rewrite (exist_destruct P) always_exist sep_exist_r.
    apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
    rewrite envs_simple_replace_sound' //; simpl.
    by rewrite right_id wand_elim_r.
  - rewrite (exist_destruct P) sep_exist_r.
    apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
    rewrite envs_simple_replace_sound' //; simpl.
    by rewrite right_id wand_elim_r.
Qed.
End tactics.

Hint Extern 0 (ToPosedProof True _ _) =>
  class_apply @to_posed_proof_True : typeclass_instances.
