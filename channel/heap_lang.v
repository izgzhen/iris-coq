Require Import mathcomp.ssreflect.ssreflect.
Require Import Autosubst.Autosubst.
Require Import prelude.option.

Set Bullet Behavior "Strict Subproofs".

Inductive expr :=
| Var (x : var)
| Lit (T : Type) (t: T)  (* arbitrary Coq values become literals *)
| App (e1 e2 : expr)
| Lam (e : {bind expr})
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr}).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive value :=
| LitV (T : Type) (t : T)  (* arbitrary Coq values become literals *)
| LamV (e : {bind expr})
| PairV (v1 v2 : value)
| InjLV (v : value)
| InjRV (v : value).

Fixpoint v2e (v : value) : expr :=
  match v with
  | LitV T t => Lit T t
  | LamV e   => Lam e
  | PairV v1 v2 => Pair (v2e v1) (v2e v2)
  | InjLV v => InjL (v2e v)
  | InjRV v => InjR (v2e v)
  end.

Fixpoint e2v (e : expr) : option value :=
  match e with
  | Var _ => None
  | Lit T t => Some (LitV T t)
  | App _ _ => None
  | Lam e => Some (LamV e)
  | Pair e1 e2 => v1 ← e2v e1;
                  v2 ← e2v e2;
                  Some (PairV v1 v2)
  | Fst e => None
  | Snd e => None
  | InjL e => InjLV <$> e2v e
  | InjR e => InjRV <$> e2v e
  | Case e0 e1 e2 => None
  end.

Lemma v2v v:
  e2v (v2e v) = Some v.
Proof.
  induction v; simpl; rewrite ?IHv ?IHv1 /= ?IHv2; reflexivity.
Qed.

Section e2e. (* To get local tactics. *)
Lemma e2e e v:
  e2v e = Some v -> e = v2e v.
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

Definition eq_transport (T1 T2: Type) (Heq: T1 = T2):
  T1 -> T2. (* RJ: I am *sure* this is already defined somewhere... *)
intros t1. rewrite -Heq. exact t1.
Defined.

Lemma eq_transport_id T (t: T) :
  t = eq_transport T T eq_refl t.
Proof.
  reflexivity.
Qed.

Lemma v2e_inj v1 v2:
  v2e v1 = v2e v2 -> v1 = v2.
Proof.
  revert v2; induction v1=>v2; destruct v2; simpl; try discriminate; case; eauto using f_equal, f_equal2.
  - intros _. move/EqdepFacts.eq_sigT_sig_eq=>H. destruct H as (->,<-). reflexivity.
Qed.

Inductive ectx :=
| EmptyCtx
| AppLCtx (K1 : ectx) (e2 : expr)
| AppRCtx (v1 : value) (K2 : ectx)
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
  e2v (fill K e) = Some v' -> exists v, e2v e = Some v.
Proof.
  revert v'; induction K => v' /=; try discriminate;
    try destruct (e2v (fill K e)); rewrite ?v2v; eauto.
Qed.

Definition state := unit.

Inductive prim_step : expr -> state -> expr -> state -> option expr -> Prop :=
| Beta e1 e2 v2 σ (Hv2 : e2v e2 = Some v2):
    prim_step (App (Lam e1) e2) σ (e1.[e2/]) σ None
| FstS e1 v1 e2 v2 σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2):
    prim_step (Fst (Pair e1 e2)) σ e1 σ None
| SndS e1 v1 e2 v2 σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2):
    prim_step (Snd (Pair e1 e2)) σ e2 σ None
| CaseL e0 v0 e1 e2 σ (Hv0 : e2v e0 = Some v0):
    prim_step (Case (InjL e0) e1 e2) σ (e1.[e0/]) σ None
| CaseR e0 v0 e1 e2 σ (Hv0 : e2v e0 = Some v0):
    prim_step (Case (InjR e0) e1 e2) σ (e2.[e0/]) σ None.

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


Lemma fill_not_value e K :
  e2v e = None -> e2v (fill K e) = None.
Proof.
  intros Hnval.  induction K =>/=; try reflexivity.
  - done.
  - by rewrite IHK /=.
  - by rewrite v2v /= IHK /=.
  - by rewrite IHK /=.
  - by rewrite IHK /=.
Qed.

Lemma fill_not_value2 e K v :
  e2v e = None -> e2v (fill K e) = Some v -> False.
Proof.
  intros Hnval Hval. erewrite fill_not_value in Hval by assumption. discriminate.
Qed.

Section step_by_value.
(* When something does a step, and another decomposition of the same
     expression has a non-value e in the hole, then K is a left
     sub-context of K' - in other words, e also contains the reducible
     expression *)
Lemma step_by_value K K' e e' :
  fill K e = fill K' e' ->
  reducible e' ->
  e2v e = None ->
  exists K'', K' = comp_ctx K K''.
Proof.
  Ltac bad_fill1 Hfill := exfalso; case: Hfill => Hfill; intros; subst; eapply fill_not_value2; first eassumption;
                          by erewrite Hfill, ?v2v.
  Ltac bad_fill2 Hfill := exfalso; case: Hfill => Hfill; intros; subst; eapply values_stuck; eassumption.
  Ltac bad_red   Hfill e' Hred := exfalso; destruct e'; try discriminate; [];
      case: Hfill; intros; subst; destruct Hred as (σ' & e'' & σ'' & ef & Hstep);
      inversion Hstep; done || (clear Hstep; subst;
      eapply fill_not_value2; last (
        try match goal with [ H : _ = fill _ _ |- _ ] => erewrite <-H end; simpl;
        repeat match goal with [ H : e2v _ = _ |- _ ] => erewrite H; simpl end
      ); eassumption || done).
  Ltac good Hfill IH := case: Hfill => Hfill; intros; subst; 
    let K'' := fresh "K''" in edestruct IH as [K'' Hcomp]; first eassumption;
    exists K''; by eauto using f_equal, f_equal2, f_equal3, v2e_inj.

  intros Hfill Hred Hnval. 
  revert K' Hfill; induction K=>K' /= Hfill; try first [
    now eexists; reflexivity
  | destruct K'; simpl; try discriminate; try first [
      bad_red Hfill e' Hred
    | bad_fill1 Hfill
    | bad_fill2 Hfill
    | good Hfill IHK
    ]
  ].
Qed.
End step_by_value.
