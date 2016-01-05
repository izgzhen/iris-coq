Require Import mathcomp.ssreflect.ssreflect.
Require Import Autosubst.Autosubst.
Require Import prelude.option iris.language.

Set Bullet Behavior "Strict Subproofs".

(** Some tactics useful when dealing with equality of sigma-like types: existT T0 t0 = existT T1 t1.
    They all assume such an equality is the first thing on the "stack" (goal). *)
Ltac case_depeq1 := let Heq := fresh "Heq" in
  case=>_ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,<-).
Ltac case_depeq2 := let Heq := fresh "Heq" in
  case=>_ _ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,Heq);
  case:Heq=>_ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,<-).
Ltac case_depeq3 := let Heq := fresh "Heq" in
  case=>_ _ _ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,Heq);
  case:Heq=>_ _ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,Heq);
  case:Heq=>_ /EqdepFacts.eq_sigT_sig_eq=>Heq;
  destruct Heq as (->,<-).

(** Expressions and values. *)
Inductive expr :=
| Var (x : var)
| Lam (e : {bind expr})
| App (e1 e2 : expr)
| Lit {T : Type} (t: T)  (* arbitrary Coq values become literals *)
| Op1  {T1 To : Type} (f : T1 -> To) (e1 : expr)
| Op2  {T1 T2 To : Type} (f : T1 -> T2 -> To) (e1 : expr) (e2 : expr)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
| Fork (e : expr).

Definition lit_unit := Lit tt.
Definition state := unit.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive value :=
| LamV (e : {bind expr})
| LitV (T : Type) (t : T)  (* arbitrary Coq values become literal values *)
| PairV (v1 v2 : value)
| InjLV (v : value)
| InjRV (v : value).

Fixpoint v2e (v : value) : expr :=
  match v with
  | LitV _ t => Lit t
  | LamV e   => Lam e
  | PairV v1 v2 => Pair (v2e v1) (v2e v2)
  | InjLV v => InjL (v2e v)
  | InjRV v => InjR (v2e v)
  end.

Fixpoint e2v (e : expr) : option value :=
  match e with
  | Lam e => Some (LamV e)
  | Lit T t => Some (LitV T t)
  | Pair e1 e2 => v1 ← e2v e1;
                  v2 ← e2v e2;
                  Some (PairV v1 v2)
  | InjL e => InjLV <$> e2v e
  | InjR e => InjRV <$> e2v e
  | _ => None
  end.

Lemma v2v v:
  e2v (v2e v) = Some v.
Proof.
  induction v; simpl; rewrite ?IHv ?IHv1 /= ?IHv2; reflexivity.
Qed.

Section e2e. (* To get local tactics. *)
Lemma e2e e v:
  e2v e = Some v -> v2e v = e.
Proof.
  Ltac case0 := case =><-; simpl; eauto using f_equal, f_equal2.
  Ltac case1 e1 := destruct (e2v e1); simpl; [|discriminate];
                   case0.
  Ltac case2 e1 e2 := destruct (e2v e1); simpl; [|discriminate];
                      destruct (e2v e2); simpl; [|discriminate];
                      case0.

  revert v; induction e; intros v; simpl; try discriminate; by (case2 e1 e2 || case1 e || case0).
Qed.
End e2e.

Lemma v2e_inj v1 v2:
  v2e v1 = v2e v2 -> v1 = v2.
Proof.
  revert v2; induction v1=>v2; destruct v2; simpl; try discriminate;
    first [case_depeq3 | case_depeq2 | case_depeq1 | case]; eauto using f_equal, f_equal2.
Qed.

(** Evaluation contexts *)
Inductive ectx :=
| EmptyCtx
| AppLCtx (K1 : ectx) (e2 : expr)
| AppRCtx (v1 : value) (K2 : ectx)
| Op1Ctx {T1 To : Type} (f : T1 -> To) (K : ectx)
| Op2LCtx {T1 T2 To : Type} (f : T1 -> T2 -> To) (K1 : ectx) (e2 : expr)
| Op2RCtx {T1 T2 To : Type} (f : T1 -> T2 -> To) (v1 : value) (K2 : ectx)
| PairLCtx (K1 : ectx) (e2 : expr)
| PairRCtx (v1 : value) (K2 : ectx)
| FstCtx (K : ectx)
| SndCtx (K : ectx)
| InjLCtx (K : ectx)
| InjRCtx (K : ectx)
| CaseCtx (K : ectx) (e1 : {bind expr}) (e2 : {bind expr}).

Fixpoint fill (K : ectx) (e : expr) :=
  match K with
  | EmptyCtx => e
  | AppLCtx K1 e2 => App (fill K1 e) e2
  | AppRCtx v1 K2 => App (v2e v1) (fill K2 e)
  | Op1Ctx _ _ f K => Op1 f (fill K e)
  | Op2LCtx _ _ _ f K1 e2 => Op2 f (fill K1 e) e2
  | Op2RCtx _ _ _ f v1 K2 => Op2 f (v2e v1) (fill K2 e)
  | PairLCtx K1 e2 => Pair (fill K1 e) e2
  | PairRCtx v1 K2 => Pair (v2e v1) (fill K2 e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  end.

Fixpoint comp_ctx (Ko : ectx) (Ki : ectx) :=
  match Ko with
  | EmptyCtx => Ki
  | AppLCtx K1 e2 => AppLCtx (comp_ctx K1 Ki) e2
  | AppRCtx v1 K2 => AppRCtx v1 (comp_ctx K2 Ki)
  | Op1Ctx _ _ f K => Op1Ctx f (comp_ctx K Ki)
  | Op2LCtx _ _ _ f K1 e2 => Op2LCtx f (comp_ctx K1 Ki) e2
  | Op2RCtx _ _ _ f v1 K2 => Op2RCtx f v1 (comp_ctx K2 Ki)
  | PairLCtx K1 e2 => PairLCtx (comp_ctx K1 Ki) e2
  | PairRCtx v1 K2 => PairRCtx v1 (comp_ctx K2 Ki)
  | FstCtx K => FstCtx (comp_ctx K Ki)
  | SndCtx K => SndCtx (comp_ctx K Ki)
  | InjLCtx K => InjLCtx (comp_ctx K Ki)
  | InjRCtx K => InjRCtx (comp_ctx K Ki)
  | CaseCtx K e1 e2 => CaseCtx (comp_ctx K Ki) e1 e2
  end.

Lemma fill_empty e :
  fill EmptyCtx e = e.
Proof.
  reflexivity.
Qed.

Lemma fill_comp K1 K2 e :
  fill K1 (fill K2 e) = fill (comp_ctx K1 K2) e.
Proof.
  revert K2 e; induction K1 => K2 e /=; rewrite ?IHK1 ?IHK2; reflexivity.
Qed.

Lemma fill_inj_r K e1 e2 :
  fill K e1 = fill K e2 -> e1 = e2.
Proof.
  revert e1 e2; induction K => el er /=;
     (move=><-; reflexivity) || (case => /IHK <-; reflexivity).
Qed.

Lemma fill_value K e v':
  e2v (fill K e) = Some v' -> is_Some (e2v e).
Proof.
  revert v'; induction K => v' /=; try discriminate;
    try destruct (e2v (fill K e)); rewrite ?v2v; eauto.
Qed.

Lemma fill_not_value e K :
  e2v e = None -> e2v (fill K e) = None.
Proof.
  intros Hnval.  induction K =>/=; by rewrite ?v2v /= ?IHK /=.
Qed.

Lemma fill_not_value2 e K v :
  e2v e = None -> e2v (fill K e) = Some v -> False.
Proof.
  intros Hnval Hval. erewrite fill_not_value in Hval by assumption. discriminate.
Qed.


(** The stepping relation *)
Inductive prim_step : expr -> state -> expr -> state -> option expr -> Prop :=
| BetaS e1 e2 v2 σ (Hv2 : e2v e2 = Some v2):
    prim_step (App (Lam e1) e2) σ (e1.[e2/]) σ None
| Op1S T1 To (f : T1 -> To) t σ:
    prim_step (Op1 f (Lit t)) σ (Lit (f t)) σ None
| Op2S T1 T2 To (f : T1 -> T2 -> To) t1 t2 σ:
    prim_step (Op2 f (Lit t1) (Lit t2)) σ (Lit (f t1 t2)) σ None
| FstS e1 v1 e2 v2 σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2):
    prim_step (Fst (Pair e1 e2)) σ e1 σ None
| SndS e1 v1 e2 v2 σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2):
    prim_step (Snd (Pair e1 e2)) σ e2 σ None
| CaseLS e0 v0 e1 e2 σ (Hv0 : e2v e0 = Some v0):
    prim_step (Case (InjL e0) e1 e2) σ (e1.[e0/]) σ None
| CaseRS e0 v0 e1 e2 σ (Hv0 : e2v e0 = Some v0):
    prim_step (Case (InjR e0) e1 e2) σ (e2.[e0/]) σ None
| ForkS e σ:
    prim_step (Fork e) σ lit_unit σ (Some e).

Definition reducible e: Prop :=
  exists σ e' σ' ef, prim_step e σ e' σ' ef.

Definition stuck (e : expr) : Prop :=
  forall K e',
    e = fill K e' ->
    ~reducible e'.

Lemma values_stuck v :
  stuck (v2e v).
Proof.
  intros ?? Heq.
  edestruct (fill_value K) as [v' Hv'].
  { by rewrite <-Heq, v2v. }
  clear -Hv'. intros (σ' & e'' & σ'' & ef & Hstep). destruct Hstep; simpl in *; discriminate.
Qed.


Section step_by_value.
(* When something does a step, and another decomposition of the same
     expression has a non-value e in the hole, then K is a left
     sub-context of K' - in other words, e also contains the reducible
     expression *)
Lemma step_by_value {K K' e e'} :
  fill K e = fill K' e' ->
  reducible e' ->
  e2v e = None ->
  exists K'', K' = comp_ctx K K''.
Proof.
  Ltac bad_fill Hfill := exfalso; move: Hfill; first [case_depeq3 | case_depeq2 | case_depeq1 | case] =>Hfill;
                         intros; subst;
                         (eapply values_stuck; eassumption) || (eapply fill_not_value2; first eassumption;
                         by erewrite ?Hfill, ?v2v).
  Ltac bad_red   Hfill e' Hred := exfalso; destruct e'; try discriminate; [];
      case: Hfill; intros; subst; destruct Hred as (σ' & e'' & σ'' & ef & Hstep);
      inversion Hstep; done || (clear Hstep; subst;
      eapply fill_not_value2; last (
        try match goal with [ H : _ = fill _ _ |- _ ] => erewrite <-H end; simpl;
        repeat match goal with [ H : e2v _ = _ |- _ ] => erewrite H; simpl end
      ); eassumption || done).
  Ltac good Hfill IH := move: Hfill; first [case_depeq3 | case_depeq2 | case_depeq1 | case]; intros; subst; 
    let K'' := fresh "K''" in edestruct IH as [K'' Hcomp]; first eassumption;
    exists K''; by eauto using f_equal, f_equal2, f_equal3, v2e_inj.

  intros Hfill Hred Hnval. 
  Time revert K' Hfill; induction K=>K' /= Hfill; try first [
    now eexists; reflexivity
  | destruct K'; simpl; try discriminate; try first [
      bad_red Hfill e' Hred
    | bad_fill Hfill
    | good Hfill IHK
    ]
  ].
Qed.
End step_by_value.

(** Atomic expressions *)
Definition atomic (e: expr) :=
  match e with
  | _ => False
  end.

(** Tests, making sure that stuff works. *)
Module Tests.
  Definition lit := Lit 21.
  Definition term := Op2 plus lit lit.

  Goal forall σ, prim_step term σ (Lit 42) σ None.
  Proof.
    apply Op2S.
  Qed.
End Tests.

(** Instantiate the Iris language interface. This closes reduction under evaluation contexts.
    We could potentially make this a generic construction. *)
Section Language.
  Local Obligation Tactic := idtac.

  Definition ectx_step e1 σ1 e2 σ2 (ef: option expr) :=
    exists K e1' e2', e1 = fill K e1' /\ e2 = fill K e2' /\ prim_step e1' σ1 e2' σ2 ef.

  Instance heap_lang : Language expr value state := Build_Language v2e e2v atomic ectx_step.
  Proof.
    - exact v2v.
    - exact e2e.
    - intros e1 σ1 e2 σ2 ef (K & e1' & e2' & He1 & He2 & Hstep). subst e1 e2.
      eapply fill_not_value. case Heq:(e2v e1') => [v1'|]; last done. exfalso.
      eapply values_stuck; last by (do 4 eexists; eassumption). erewrite fill_empty.
      eapply e2e. eassumption.
    - intros. contradiction.
    - intros. contradiction.
  Defined.

  (** We can have bind with arbitrary evaluation contexts **)
  Lemma fill_is_ctx K: is_ctx (fill K).
  Proof.
    split; last split.
    - intros ? [v Hval]. eapply fill_value. eassumption.
    - intros ? ? ? ? ? (K' & e1' & e2' & Heq1 & Heq2 & Hstep).
      exists (comp_ctx K K'), e1', e2'. rewrite -!fill_comp Heq1 Heq2.
      split; last split; reflexivity || assumption.
    - intros ? ? ? ? ? Hnval (K'' & e1'' & e2'' & Heq1 & Heq2 & Hstep).
      destruct (step_by_value Heq1) as [K' HeqK].
      + do 4 eexists. eassumption.
      + assumption.
      + subst e2 K''. rewrite -fill_comp in Heq1. apply fill_inj_r in Heq1. subst e1'.
        exists (fill K' e2''). split; first by rewrite -fill_comp.
        do 3 eexists. split; last split; eassumption || reflexivity.
  Qed.

End Language.
