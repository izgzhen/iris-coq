Require Export Autosubst.Autosubst.
Require Import prelude.option prelude.gmap iris.language.

(** Some tactics useful when dealing with equality of sigma-like types:
    existT T0 t0 = existT T1 t1.
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
Definition loc := positive. (* Really, any countable type. *)

Inductive expr :=
(* Base lambda calculus *)
| Var (x : var)
| Rec (e : {bind 2 of expr}) (* These are recursive lambdas. The *inner* binder is the recursive call! *)
| App (e1 e2 : expr)
(* Embedding of Coq values and operations *)
| Lit {T : Type} (t: T)  (* arbitrary Coq values become literals *)
| Op1  {T1 To : Type} (f : T1 → To) (e1 : expr)
| Op2  {T1 T2 To : Type} (f : T1 → T2 → To) (e1 : expr) (e2 : expr)
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
(* Concurrency *)
| Fork (e : expr)
(* Heap *)
| Loc (l : loc)
| Alloc (e : expr)
| Load (e : expr)
| Store (e1 : expr) (e2 : expr)
| Cas (e0 : expr) (e1 : expr) (e2 : expr)
.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Definition Lam (e: {bind expr}) := Rec (e.[ren(+1)]).
Definition Let' (e1: expr) (e2: {bind expr}) := App (Lam e2) e1.
Definition Seq (e1 e2: expr) := Let' e1 (e2.[ren(+1)]).

Inductive value :=
| RecV (e : {bind 2 of expr})
| LitV {T : Type} (t : T)  (* arbitrary Coq values become literal values *)
| PairV (v1 v2 : value)
| InjLV (v : value)
| InjRV (v : value)
| LocV (l : loc)
.

Definition LitUnit := Lit tt.
Definition LitVUnit := LitV tt.
Definition LitTrue := Lit true.
Definition LitVTrue := LitV true.
Definition LitFalse := Lit false.
Definition LitVFalse := LitV false.

Fixpoint v2e (v : value) : expr :=
  match v with
  | LitV _ t => Lit t
  | RecV e   => Rec e
  | PairV v1 v2 => Pair (v2e v1) (v2e v2)
  | InjLV v => InjL (v2e v)
  | InjRV v => InjR (v2e v)
  | LocV l => Loc l
  end.

Fixpoint e2v (e : expr) : option value :=
  match e with
  | Rec e => Some (RecV e)
  | Lit _ t => Some (LitV t)
  | Pair e1 e2 => v1 ← e2v e1;
                  v2 ← e2v e2;
                  Some (PairV v1 v2)
  | InjL e => InjLV <$> e2v e
  | InjR e => InjRV <$> e2v e
  | Loc l => Some (LocV l)
  | _ => None
  end.

Lemma v2v v:
  e2v (v2e v) = Some v.
Proof.
  induction v; simpl; rewrite ?IHv ?IHv1 /= ?IHv2; reflexivity.
Qed.

Section e2e. (* To get local tactics. *)
Lemma e2e e v:
  e2v e = Some v → v2e v = e.
Proof.
  Ltac case0 := case =><-; simpl; eauto using f_equal, f_equal2.
  Ltac case1 e1 := destruct (e2v e1); simpl; [|discriminate];
                   case0.
  Ltac case2 e1 e2 := destruct (e2v e1); simpl; [|discriminate];
                      destruct (e2v e2); simpl; [|discriminate];
                      case0.

  revert v; induction e; intros v; simpl; try discriminate;
    by (case2 e1 e2 || case1 e || case0).
Qed.
End e2e.

Lemma v2e_inj v1 v2:
  v2e v1 = v2e v2 → v1 = v2.
Proof.
  revert v2; induction v1=>v2; destruct v2; simpl; try discriminate;
    first [case_depeq1 | case]; eauto using f_equal, f_equal2.
Qed.

(** The state: heaps of values. *)
Definition state := gmap loc value.

(** Evaluation contexts *)
Inductive ectx :=
| EmptyCtx
| AppLCtx (K1 : ectx)  (e2 : expr)
| AppRCtx (v1 : value) (K2 : ectx)
| Op1Ctx {T1 To : Type} (f : T1 -> To) (K : ectx)
| Op2LCtx {T1 T2 To : Type} (f : T1 -> T2 -> To) (K1 : ectx)  (e2 : expr)
| Op2RCtx {T1 T2 To : Type} (f : T1 -> T2 -> To) (v1 : value) (K2 : ectx)
| PairLCtx (K1 : ectx)  (e2 : expr)
| PairRCtx (v1 : value) (K2 : ectx)
| FstCtx (K : ectx)
| SndCtx (K : ectx)
| InjLCtx (K : ectx)
| InjRCtx (K : ectx)
| CaseCtx (K : ectx) (e1 : {bind expr}) (e2 : {bind expr})
| AllocCtx (K : ectx)
| LoadCtx (K : ectx)
| StoreLCtx (K1 : ectx)  (e2 : expr)
| StoreRCtx (v1 : value) (K2 : ectx)
| CasLCtx (K0 : ectx)  (e1 : expr)  (e2 : expr)
| CasMCtx (v0 : value) (K1 : ectx)  (e2 : expr)
| CasRCtx (v0 : value) (v1 : value) (K2 : ectx)
.

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
  | AllocCtx K => Alloc (fill K e)
  | LoadCtx K => Load (fill K e)
  | StoreLCtx K1 e2 => Store (fill K1 e) e2
  | StoreRCtx v1 K2 => Store (v2e v1) (fill K2 e)
  | CasLCtx K0 e1 e2 => Cas (fill K0 e) e1 e2
  | CasMCtx v0 K1 e2 => Cas (v2e v0) (fill K1 e) e2
  | CasRCtx v0 v1 K2 => Cas (v2e v0) (v2e v1) (fill K2 e)
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
  | AllocCtx K => AllocCtx (comp_ctx K Ki)
  | LoadCtx K => LoadCtx (comp_ctx K Ki)
  | StoreLCtx K1 e2 => StoreLCtx (comp_ctx K1 Ki) e2
  | StoreRCtx v1 K2 => StoreRCtx v1 (comp_ctx K2 Ki)
  | CasLCtx K0 e1 e2 => CasLCtx (comp_ctx K0 Ki) e1 e2
  | CasMCtx v0 K1 e2 => CasMCtx v0 (comp_ctx K1 Ki) e2
  | CasRCtx v0 v1 K2 => CasRCtx v0 v1 (comp_ctx K2 Ki)
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
  fill K e1 = fill K e2 → e1 = e2.
Proof.
  revert e1 e2; induction K => el er /=;
     (move=><-; reflexivity) || (case => /IHK <-; reflexivity).
Qed.

Lemma fill_value K e v':
  e2v (fill K e) = Some v' → is_Some (e2v e).
Proof.
  revert v'; induction K => v' /=; try discriminate;
    try destruct (e2v (fill K e)); rewrite ?v2v; eauto.
Qed.

Lemma fill_not_value e K :
  e2v e = None → e2v (fill K e) = None.
Proof.
  intros Hnval.  induction K =>/=; by rewrite ?v2v /= ?IHK /=.
Qed.

Lemma fill_not_value2 e K v :
  e2v e = None → e2v (fill K e) = Some v -> False.
Proof.
  intros Hnval Hval. erewrite fill_not_value in Hval by assumption. discriminate.
Qed.

Lemma comp_empty K K' :
  EmptyCtx = comp_ctx K K' →
  K = EmptyCtx ∧ K' = EmptyCtx.
Proof.
  destruct K; try discriminate.
  destruct K'; try discriminate.
  done.
Qed.

(** The stepping relation *)
Inductive prim_step : expr -> state -> expr -> state -> option expr -> Prop :=
| BetaS e1 e2 v2 σ (Hv2 : e2v e2 = Some v2):
    prim_step (App (Rec e1) e2) σ (e1.[(Rec e1),e2/]) σ None
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
    prim_step (Fork e) σ LitUnit σ (Some e)
| AllocS e v σ l (Hv : e2v e = Some v) (Hfresh : σ !! l = None):
    prim_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None
| LoadS l v σ (Hlookup : σ !! l = Some v):
    prim_step (Load (Loc l)) σ (v2e v) σ None
| StoreS l e v σ (Hv : e2v e = Some v) (Halloc : is_Some (σ !! l)):
    prim_step (Store (Loc l) e) σ LitUnit (<[l:=v]>σ) None
| CasFailS l e1 v1 e2 v2 vl σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2)
  (Hlookup : σ !! l = Some vl) (Hne : vl <> v1):
    prim_step (Cas (Loc l) e1 e2) σ LitFalse σ None
| CasSucS l e1 v1 e2 v2 σ (Hv1 : e2v e1 = Some v1) (Hv2 : e2v e2 = Some v2)
  (Hlookup : σ !! l = Some v1):
    prim_step (Cas (Loc l) e1 e2) σ LitTrue (<[l:=v2]>σ) None
.

Definition reducible e σ : Prop :=
  ∃ e' σ' ef, prim_step e σ e' σ' ef.

Lemma reducible_not_value e σ :
  reducible e σ → e2v e = None.
Proof.
  intros (e' & σ' & ef & Hstep). destruct Hstep; simpl in *; reflexivity.
Qed.

Definition stuck (e : expr) σ : Prop :=
  ∀ K e', e = fill K e' → ~reducible e' σ.

Lemma values_stuck v σ :
  stuck (v2e v) σ.
Proof.
  intros ?? Heq.
  edestruct (fill_value K) as [v' Hv'].
  { by rewrite <-Heq, v2v. }
  clear -Hv' => Hred. apply reducible_not_value in Hred.
  destruct (e2v e'); discriminate.
Qed.

Section step_by_value.
(* When something does a step, and another decomposition of the same
     expression has a non-value e in the hole, then K is a left
     sub-context of K' - in other words, e also contains the reducible
     expression *)
Lemma step_by_value {K K' e e' σ} :
  fill K e = fill K' e' →
  reducible e' σ →
  e2v e = None →
  ∃ K'', K' = comp_ctx K K''.
Proof.
  Ltac bad_fill := intros; exfalso; subst;
                   (eapply values_stuck; eassumption) ||
                     (eapply fill_not_value2; first eassumption;
                      try match goal with
                        [ H : fill _ _ = _ |- _ ] => erewrite ->H
                      end;
                      by erewrite ?v2v).
  Ltac bad_red   Hfill e' Hred := exfalso; destruct e';
      try discriminate Hfill; [];
      case: Hfill; intros; subst; destruct Hred as (e'' & σ'' & ef & Hstep);
      inversion Hstep; done || (clear Hstep; subst;
      eapply fill_not_value2; last (
        try match goal with [ H : _ = fill _ _ |- _ ] => erewrite <-H end; simpl;
        repeat match goal with [ H : e2v _ = _ |- _ ] =>
          erewrite H; clear H; simpl
        end
      ); eassumption || done).
  Ltac good IH := intros; subst; 
    let K'' := fresh "K''" in edestruct IH as [K'' Hcomp]; first eassumption;
    exists K''; by eauto using f_equal, f_equal2, f_equal3, v2e_inj.

  intros Hfill Hred Hnval. 
  revert K' Hfill; induction K=>K' /= Hfill;
    first (now eexists; reflexivity);
    (destruct K'; simpl;
      (* The first case is: K' is EmpyCtx. *)
      first (by bad_red Hfill e' Hred);
      (* Many of the other cases result in contradicting equalities. *)
      try discriminate Hfill;
      (* The remaining cases are "compatible" contexts - that result in the same
         head symbol of the expression.
         Test whether the context als has the same head, and use the appropriate
         tactic. Furthermore, the Op* contexts need special treatment due to the
         inhomogenuous equalities they induce. *)
      by match goal with
      | [ |- exists x, Op1Ctx _ _ = Op1Ctx _ _ ] =>
        move: Hfill; case_depeq2; good IHK
      | [ |- exists x, Op2LCtx _ _ _ = Op2LCtx _ _ _ ] =>
        move: Hfill; case_depeq3; good IHK
      | [ |- exists x, Op2RCtx _ _ _ = Op2RCtx _ _ _ ] =>
        move: Hfill; case_depeq3; good IHK
      | [ |- exists x, ?C _ = ?C _ ] =>
        case: Hfill; good IHK
      | [ |- exists x, ?C _ _ = ?C _ _ ] =>
        case: Hfill; good IHK
      | [ |- exists x, ?C _ _ _ = ?C _ _ _ ] =>
        case: Hfill; good IHK
      | [ |- exists x, Op2LCtx _ _ _ = Op2RCtx _ _ _ ] =>
        move: Hfill; case_depeq3; bad_fill
      | [ |- exists x, Op2RCtx _ _ _ = Op2LCtx _ _ _ ] =>
        move: Hfill; case_depeq3; bad_fill
      | _ => case: Hfill; bad_fill
      end).
Qed.
End step_by_value.

(** Atomic expressions *)
Definition atomic (e: expr) :=
  match e with
  | Alloc e => is_Some (e2v e)
  | Load e => is_Some (e2v e)
  | Store e1 e2 => is_Some (e2v e1) ∧ is_Some (e2v e2)
  | Cas e0 e1 e2 => is_Some (e2v e0) ∧ is_Some (e2v e1) ∧ is_Some (e2v e2)
  | _ => False
  end.

Lemma atomic_not_value e :
  atomic e -> e2v e = None.
Proof.
  destruct e; simpl; contradiction || reflexivity.
Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 →
  prim_step e1 σ1 e2 σ2 ef →
  is_Some (e2v e2).
Proof.
  destruct e1; simpl; intros Hatomic Hstep; inversion Hstep;
    try contradiction Hatomic; rewrite ?v2v /=; eexists; reflexivity.
Qed.

(* Atomics must not contain evaluation positions. *)
Lemma atomic_fill e K :
  atomic (fill K e) →
  e2v e = None →
  K = EmptyCtx.
Proof.
  destruct K; simpl; first reflexivity; unfold is_Some; intros Hatomic Hnval;
    exfalso; try assumption;
    try (destruct_conjs; eapply fill_not_value2; eassumption).
Qed.

(** Instantiate the Iris language interface. This closes reduction under
    evaluation contexts.
    We could potentially make this a generic construction. *)
Section Language.

  Definition ectx_step e1 σ1 e2 σ2 (ef: option expr) :=
    ∃ K e1' e2', e1 = fill K e1' ∧ e2 = fill K e2' ∧
                 prim_step e1' σ1 e2' σ2 ef.

  Global Program Instance heap_lang : Language expr value state := {|
    of_val := v2e;
    to_val := e2v;
    language.atomic := atomic;
    language.prim_step := ectx_step;
    to_of_val := v2v;
    of_to_val := e2e;
    language.atomic_not_value := atomic_not_value
  |}.
  Next Obligation.
    intros e1 σ1 e2 σ2 ef (K & e1' & e2' & He1 & He2 & Hstep). subst e1 e2.
    eapply fill_not_value. eapply reducible_not_value. do 3 eexists; eassumption.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? Hatomic (K & e1' & e2' & Heq1 & Heq2 & Hstep).
    subst. move: (Hatomic). rewrite (atomic_fill e1' K).
    - rewrite !fill_empty. eauto using atomic_step.
    - assumption.
    - clear Hatomic. eapply reducible_not_value. do 3 eexists; eassumption.
  Qed.

  (** We can have bind with arbitrary evaluation contexts **)
  Lemma fill_is_ctx K: is_ctx (fill K).
  Proof.
    split.
    - intros ? Hnval. by eapply fill_not_value.
    - intros ? ? ? ? ? (K' & e1' & e2' & Heq1 & Heq2 & Hstep).
      exists (comp_ctx K K'), e1', e2'. rewrite -!fill_comp Heq1 Heq2.
      split; last split; reflexivity || assumption.
    - intros ? ? ? ? ? Hnval (K'' & e1'' & e2'' & Heq1 & Heq2 & Hstep).
      destruct (step_by_value (σ:=σ1) Heq1) as [K' HeqK].
      + do 3 eexists. eassumption.
      + assumption.
      + subst e2 K''. rewrite -fill_comp in Heq1. apply fill_inj_r in Heq1.
        subst e1'. exists (fill K' e2''). split; first by rewrite -fill_comp.
        do 3 eexists. split; last split; eassumption || reflexivity.
  Qed.

  Lemma prim_ectx_step e1 σ1 e2 σ2 ef :
    reducible e1 σ1 →
    ectx_step e1 σ1 e2 σ2 ef →
    prim_step e1 σ1 e2 σ2 ef.
  Proof.
    intros Hred (K' & e1' & e2' & Heq1 & Heq2 & Hstep).
    destruct (@step_by_value K' EmptyCtx e1' e1 σ1) as [K'' [HK' HK'']%comp_empty].
    - by rewrite fill_empty.
    - done.
    - eapply reducible_not_value. do 3 eexists; eassumption.
    - subst K' K'' e1 e2. by rewrite !fill_empty.
  Qed.

End Language.
