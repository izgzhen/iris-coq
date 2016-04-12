From iris.prelude Require Export strings.
From iris.algebra Require Export base.
From iris.prelude Require Import stringmap.

Inductive env (A : Type) : Type :=
  | Enil : env A
  | Esnoc : env A → string → A → env A.
Arguments Enil {_}.
Arguments Esnoc {_} _ _%string _.

Local Notation "x ← y ; z" := (match y with Some x => z | None => None end).
Local Notation "' ( x1 , x2 ) ← y ; z" :=
  (match y with Some (x1,x2) => z | None => None end).
Local Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (match y with Some (x1,x2,x3) => z | None => None end).

Fixpoint env_lookup {A} (i : string) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x => if decide (i = j) then Some x else env_lookup i Γ
  end.
Local Notation "Γ !! j" := (env_lookup j Γ).

Inductive env_wf {A} : env A → Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf Γ i x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ i x).

Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with Enil => [] | Esnoc Γ _ x => x :: env_to_list Γ end.
Coercion env_to_list : env >-> list.

Instance env_dom {A} : Dom (env A) stringset :=
  fix go Γ := let _ : Dom _ _ := @go in
  match Γ with Enil => ∅ | Esnoc Γ i _ => {[ i ]} ∪ dom stringset Γ end.
Fixpoint env_dom_list {A} (Γ : env A) : list string :=
  match Γ with Enil => [] | Esnoc Γ i _ => i :: env_dom_list Γ end.

Fixpoint env_fold {A B} (f : B → A → A) (x : A) (Γ : env B) : A :=
  match Γ with
  | Enil => x
  | Esnoc Γ _ y => env_fold f (f y x) Γ
  end.

Fixpoint env_app {A} (Γapp : env A) (Γ : env A) : option (env A) :=
  match Γapp with
  | Enil => Some Γ
  | Esnoc Γapp i x =>
     Γ' ← env_app Γapp Γ; 
     match Γ' !! i with None => Some (Esnoc Γ' i x) | Some _ => None end
  end.
Fixpoint env_replace {A} (i: string) (Γi: env A) (Γ: env A) : option (env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if decide (i = j) then env_app Γi Γ else
     match Γi !! j with
     | None => Γ' ← env_replace i Γi Γ; Some (Esnoc Γ' j x)
     | Some _ => None
     end
  end.
Fixpoint env_delete {A} (i : string) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ j x => if decide (i = j) then Γ else Esnoc (env_delete i Γ) j x
  end.
Fixpoint env_lookup_delete {A} (i : string) (Γ : env A) : option (A * env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if decide (i = j) then Some (x,Γ)
     else '(y,Γ') ← env_lookup_delete i Γ; Some (y, Esnoc Γ' j x)
  end.
Fixpoint env_split_go {A} (js : list string)
    (Γ1 Γ2 : env A) : option (env A * env A) :=
  match js with
  | [] => Some (Γ1, Γ2)
  | j::js => '(x,Γ2) ← env_lookup_delete j Γ2; env_split_go js (Esnoc Γ1 j x) Γ2
  end.
Definition env_split {A} (js : list string)
  (Γ : env A) : option (env A * env A) := env_split_go js Enil Γ.

Inductive env_Forall2 {A B} (P : A → B → Prop) : env A → env B → Prop :=
  | env_Forall2_nil : env_Forall2 P Enil Enil
  | env_Forall2_snoc Γ1 Γ2 i x y :
     env_Forall2 P Γ1 Γ2 → P x y → env_Forall2 P (Esnoc Γ1 i x) (Esnoc Γ2 i y).

Section env.
Context {A : Type}.
Implicit Types Γ : env A.
Implicit Types i : string.
Implicit Types x : A.
Hint Resolve Esnoc_wf Enil_wf.

Ltac simplify := repeat (case_match || simplify_option_eq).

Lemma env_lookup_perm Γ i x : Γ !! i = Some x → Γ ≡ₚ x :: env_delete i Γ.
Proof.
  induction Γ; intros; simplify; rewrite 1?Permutation_swap; f_equiv; eauto.
Qed.

Lemma env_app_perm Γ Γapp Γ' :
  env_app Γapp Γ = Some Γ' → env_to_list Γ' ≡ₚ Γapp ++ Γ.
Proof. revert Γ'; induction Γapp; intros; simplify; f_equal; auto. Qed.
Lemma env_app_fresh Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None → Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_fresh_1 Γ Γapp Γ' i x :
  env_app Γapp Γ = Some Γ' → Γ' !! i = None → Γ !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_disjoint Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None ∨ Γ !! i = None.
Proof.
  revert Γ'.
  induction Γapp; intros; simplify; naive_solver eauto using env_app_fresh_1.
Qed.
Lemma env_app_wf Γ Γapp Γ' : env_app Γapp Γ = Some Γ' → env_wf Γ → env_wf Γ'.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.

Lemma env_replace_fresh Γ Γj Γ' i j :
  env_replace j Γj Γ = Some Γ' →
  Γj !! i = None → env_delete j Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γ; intros; simplify; eauto using env_app_fresh. Qed.
Lemma env_replace_wf Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → env_wf (env_delete i Γ) → env_wf Γ'.
Proof.
  revert Γ'. induction Γ; intros ??; simplify; [|inversion_clear 1];
    eauto using env_app_wf, env_replace_fresh.
Qed.
Lemma env_replace_lookup Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → is_Some (Γ !! i).
Proof. revert Γ'. induction Γ; intros; simplify; eauto. Qed.
Lemma env_replace_perm Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → Γ' ≡ₚ Γi ++ env_delete i Γ.
Proof.
  revert Γ'. induction Γ as [|Γ IH j y]=>Γ' ?; simplify_eq/=.
  destruct (decide (i = j)); simplify_eq/=; auto using env_app_perm.
  destruct (Γi !! j), (env_replace i Γi Γ) as [Γ''|] eqn:?; simplify_eq/=.
  rewrite -Permutation_middle; f_equiv; eauto.
Qed.

Lemma env_lookup_delete_correct Γ i :
  env_lookup_delete i Γ = x ← Γ !! i; Some (x,env_delete i Γ).
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_lookup_delete_Some Γ Γ' i x :
  env_lookup_delete i Γ = Some (x,Γ') ↔ Γ !! i = Some x ∧ Γ' = env_delete i Γ.
Proof. rewrite env_lookup_delete_correct; simplify; naive_solver. Qed.
Lemma env_delete_fresh_eq Γ j : env_wf Γ → env_delete j Γ !! j = None.
Proof. induction 1; intros; simplify; eauto. Qed.
Lemma env_delete_fresh Γ i j : Γ !! i = None → env_delete j Γ !! i = None.
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_delete_wf Γ j : env_wf Γ → env_wf (env_delete j Γ).
Proof. induction 1; simplify; eauto using env_delete_fresh. Qed.

Lemma env_split_fresh Γ1 Γ2 Γ1' Γ2' js i :
  env_split_go js Γ1 Γ2 = Some (Γ1',Γ2') →
  Γ1 !! i = None → Γ2 !! i = None → Γ1' !! i = None ∧ Γ2' !! i = None.
Proof.
  revert Γ1 Γ2.
  induction js as [|j js IH]=> Γ1 Γ2 ???; simplify_eq/=; eauto.
  destruct (env_lookup_delete j Γ2) as [[x Γ2'']|] eqn:Hdelete; simplify_eq/=.
  apply env_lookup_delete_Some in Hdelete as [? ->].
  eapply IH; eauto; simplify; eauto using env_delete_fresh.
Qed.
Lemma env_split_go_wf Γ1 Γ2 Γ1' Γ2' js :
  env_split_go js Γ1 Γ2 = Some (Γ1',Γ2') →
  (∀ i, Γ1 !! i = None ∨ Γ2 !! i = None) →
  env_wf Γ1 → env_wf Γ2 → env_wf Γ1' ∧ env_wf Γ2'.
Proof.
  revert Γ1 Γ2.
  induction js as [|j js IH]=> Γ1 Γ2 ? Hdisjoint ??; simplify_eq/=; auto.
  destruct (env_lookup_delete j Γ2) as [[x Γ2'']|] eqn:Hdelete; simplify_eq/=.
  apply env_lookup_delete_Some in Hdelete as [? ->].
  eapply IH; eauto using env_delete_wf.
  - intros i; simplify; eauto using env_delete_fresh_eq.
    destruct (Hdisjoint i); eauto using env_delete_fresh.  
  - constructor; auto.
    destruct (Hdisjoint j) as [?|[]%eq_None_not_Some]; eauto.
Qed.
Lemma env_split_go_perm Γ1 Γ2 Γ1' Γ2' js :
  env_split_go js Γ1 Γ2 = Some (Γ1',Γ2') → Γ1 ++ Γ2 ≡ₚ Γ1' ++ Γ2'.
Proof.
  revert Γ1 Γ2. induction js as [|j js IH]=> Γ1 Γ2 ?; simplify_eq/=; auto.
  destruct (env_lookup_delete j Γ2) as [[x Γ2'']|] eqn:Hdelete; simplify_eq/=.
  apply env_lookup_delete_Some in Hdelete as [? ->].
  by rewrite -(IH (Esnoc _ _ _) (env_delete _ _)) //=
    Permutation_middle -env_lookup_perm.
Qed.

Lemma env_split_fresh_1 Γ Γ1 Γ2 js i :
  env_split js Γ = Some (Γ1,Γ2) → Γ !! i = None → Γ1 !! i = None.
Proof. intros. by apply (env_split_fresh Enil Γ Γ1 Γ2 js). Qed.
Lemma env_split_fresh_2 Γ Γ1 Γ2 js i :
  env_split js Γ = Some (Γ1,Γ2) → Γ !! i = None → Γ2 !! i = None.
Proof. intros. by apply (env_split_fresh Enil Γ Γ1 Γ2 js). Qed.
Lemma env_split_wf_1 Γ Γ1 Γ2 js :
  env_split js Γ = Some (Γ1,Γ2) → env_wf Γ → env_wf Γ1.
Proof. intros. apply (env_split_go_wf Enil Γ Γ1 Γ2 js); eauto. Qed.
Lemma env_split_wf_2 Γ Γ1 Γ2 js :
  env_split js Γ = Some (Γ1,Γ2) → env_wf Γ → env_wf Γ2.
Proof. intros. apply (env_split_go_wf Enil Γ Γ1 Γ2 js); eauto. Qed.
Lemma env_split_perm Γ Γ1 Γ2 js : env_split js Γ = Some (Γ1,Γ2) → Γ ≡ₚ Γ1 ++ Γ2.
Proof. apply env_split_go_perm. Qed.

Lemma env_Forall2_fresh {B} (P : A → B → Prop) Γ Σ i :
  env_Forall2 P Γ Σ → Γ !! i = None → Σ !! i = None.
Proof. by induction 1; simplify. Qed.
Lemma env_Forall2_wf {B} (P : A → B → Prop) Γ Σ :
  env_Forall2 P Γ Σ → env_wf Γ → env_wf Σ.
Proof. induction 1; inversion_clear 1; eauto using env_Forall2_fresh. Qed.
End env.
