From algebra Require Export upred.
From algebra Require Export upred_big_op.
Import uPred.

Module uPred_reflection. Section uPred_reflection.
  Context {M : cmraT}.

  Inductive expr :=
    | ETrue : expr
    | EVar : nat → expr
    | ESep : expr → expr → expr.
  Fixpoint eval (Σ : list (uPred M)) (e : expr) : uPred M :=
    match e with
    | ETrue => True
    | EVar n => from_option True%I (Σ !! n)
    | ESep e1 e2 => eval Σ e1 ★ eval Σ e2
    end.
  Fixpoint flatten (e : expr) : list nat :=
    match e with
    | ETrue => []
    | EVar n => [n]
    | ESep e1 e2 => flatten e1 ++ flatten e2
    end.

  Notation eval_list Σ l :=
    (uPred_big_sep ((λ n, from_option True%I (Σ !! n)) <$> l)).
  Lemma eval_flatten Σ e : eval Σ e ≡ eval_list Σ (flatten e).
  Proof.
    induction e as [| |e1 IH1 e2 IH2];
      rewrite /= ?right_id ?fmap_app ?big_sep_app ?IH1 ?IH2 //. 
  Qed.
  Lemma flatten_entails Σ e1 e2 :
    flatten e2 `contains` flatten e1 → eval Σ e1 ⊑ eval Σ e2.
  Proof.
    intros. rewrite !eval_flatten. by apply big_sep_contains, fmap_contains.
  Qed.
  Lemma flatten_equiv Σ e1 e2 :
    flatten e2 ≡ₚ flatten e1 → eval Σ e1 ≡ eval Σ e2.
  Proof. intros He. by rewrite !eval_flatten He. Qed.

  Fixpoint prune (e : expr) : expr :=
    match e with
    | ETrue => ETrue
    | EVar n => EVar n
    | ESep e1 e2 =>
       match prune e1, prune e2 with
       | ETrue, e2' => e2'
       | e1', ETrue => e1'
       | e1', e2' => ESep e1' e2'
       end
    end.
  Lemma flatten_prune e : flatten (prune e) = flatten e.
  Proof.
    induction e as [| |e1 IH1 e2 IH2]; simplify_eq/=; auto.
    rewrite -IH1 -IH2. by repeat case_match; rewrite ?right_id_L.
  Qed.
  Lemma prune_correct Σ e : eval Σ (prune e) ≡ eval Σ e.
  Proof. by rewrite !eval_flatten flatten_prune. Qed.

  Fixpoint cancel_go (n : nat) (e : expr) : option expr :=
    match e with
    | ETrue => None
    | EVar n' => if decide (n = n') then Some ETrue else None
    | ESep e1 e2 => 
       match cancel_go n e1 with
       | Some e1' => Some (ESep e1' e2)
       | None => ESep e1 <$> cancel_go n e2
       end
    end.
  Definition cancel (ns : list nat) (e: expr) : option expr :=
    prune <$> fold_right (mbind ∘ cancel_go) (Some e) ns.
  Lemma flatten_cancel_go e e' n :
    cancel_go n e = Some e' → flatten e ≡ₚ n :: flatten e'.
  Proof.
    revert e'; induction e as [| |e1 IH1 e2 IH2]; intros;
      repeat (simplify_option_eq || case_match); auto.
    - by rewrite IH1 //.
    - by rewrite IH2 // Permutation_middle.
  Qed.
  Lemma flatten_cancel e e' ns :
    cancel ns e = Some e' → flatten e ≡ₚ ns ++ flatten e'.
  Proof.
    rewrite /cancel fmap_Some=> -[{e'}e' [He ->]]; rewrite flatten_prune.
    revert e' He; induction ns as [|n ns IH]=> e' He; simplify_option_eq; auto.
    rewrite Permutation_middle -flatten_cancel_go //; eauto.
  Qed.
  Lemma cancel_entails Σ e1 e2 e1' e2' ns :
    cancel ns e1 = Some e1' → cancel ns e2 = Some e2' →
    eval Σ e1' ⊑ eval Σ e2' → eval Σ e1 ⊑ eval Σ e2.
  Proof.
    intros ??. rewrite !eval_flatten.
    rewrite (flatten_cancel e1 e1' ns) // (flatten_cancel e2 e2' ns) //; csimpl.
    rewrite !fmap_app !big_sep_app. apply sep_mono_r.
  Qed.

  Fixpoint to_expr (l : list nat) : expr :=
    match l with
    | [] => ETrue
    | [n] => EVar n
    | n :: l => ESep (EVar n) (to_expr l)
    end.
  Arguments to_expr !_ / : simpl nomatch.
  Lemma eval_to_expr Σ l : eval Σ (to_expr l) ≡ eval_list Σ l.
  Proof.
    induction l as [|n1 [|n2 l] IH]; csimpl; rewrite ?right_id //.
    by rewrite IH.
  Qed.

  Lemma split_l Σ e ns e' :
    cancel ns e = Some e' → eval Σ e ≡ (eval Σ (to_expr ns) ★ eval Σ e')%I.
  Proof.
    intros He%flatten_cancel.
    by rewrite eval_flatten He fmap_app big_sep_app eval_to_expr eval_flatten.
  Qed.
  Lemma split_r Σ e ns e' :
    cancel ns e = Some e' → eval Σ e ≡ (eval Σ e' ★ eval Σ (to_expr ns))%I.
  Proof. intros. rewrite /= comm. by apply split_l. Qed.

  Class Quote (Σ1 Σ2 : list (uPred M)) (P : uPred M) (e : expr) := {}.
  Global Instance quote_True Σ : Quote Σ Σ True ETrue.
  Global Instance quote_var Σ1 Σ2 P i:
    rlist.QuoteLookup Σ1 Σ2 P i → Quote Σ1 Σ2 P (EVar i) | 1000.
  Global Instance quote_sep Σ1 Σ2 Σ3 P1 P2 e1 e2 :
    Quote Σ1 Σ2 P1 e1 → Quote Σ2 Σ3 P2 e2 → Quote Σ1 Σ3 (P1 ★ P2) (ESep e1 e2).

  Class QuoteArgs (Σ: list (uPred M)) (Ps: list (uPred M)) (ns: list nat) := {}.
  Global Instance quote_args_nil Σ : QuoteArgs Σ nil nil.
  Global Instance quote_args_cons Σ Ps P ns n :
    rlist.QuoteLookup Σ Σ P n →
    QuoteArgs Σ Ps ns → QuoteArgs Σ (P :: Ps) (n :: ns).
  End uPred_reflection.

  Ltac quote :=
    match goal with
    | |- ?P1 ⊑ ?P2 =>
      lazymatch type of (_ : Quote [] _ P1 _) with Quote _ ?Σ2 _ ?e1 =>
      lazymatch type of (_ : Quote Σ2 _ P2 _) with Quote _ ?Σ3 _ ?e2 =>
        change (eval Σ3 e1 ⊑ eval Σ3 e2) end end
    end.
  Ltac quote_l :=
    match goal with
    | |- ?P1 ⊑ ?P2 =>
      lazymatch type of (_ : Quote [] _ P1 _) with Quote _ ?Σ2 _ ?e1 =>
        change (eval Σ2 e1 ⊑ P2) end
    end.
End uPred_reflection.

Tactic Notation "solve_sep_entails" :=
  uPred_reflection.quote; apply uPred_reflection.flatten_entails;
  apply (bool_decide_unpack _); vm_compute; exact Logic.I.

Ltac close_uPreds Ps tac :=
  let M := match goal with |- @uPred_entails ?M _ _ => M end in
  let rec go Ps Qs :=
    lazymatch Ps with
    | [] => let Qs' := eval cbv [reverse rev_append] in (reverse Qs) in tac Qs'
    | ?P :: ?Ps => find_pat P ltac:(fun Q => go Ps (Q :: Qs))
    end in
  (* avoid evars in case Ps = @nil ?A *)
  try match Ps with [] => unify Ps (@nil (uPred M)) end;
  go Ps (@nil (uPred M)).

Tactic Notation "cancel" constr(Ps) :=
  uPred_reflection.quote;
  let Σ := match goal with |- uPred_reflection.eval ?Σ _ ⊑ _ => Σ end in
  let ns' := lazymatch type of (_ : uPred_reflection.QuoteArgs Σ Ps _) with
             | uPred_reflection.QuoteArgs _ _ ?ns' => ns'
             end in
  eapply uPred_reflection.cancel_entails with (ns:=ns');
    [cbv; reflexivity|cbv; reflexivity|simpl].

Tactic Notation "ecancel" open_constr(Ps) :=
  close_uPreds Ps ltac:(fun Qs => cancel Qs).

(** [to_front [P1, P2, ..]] rewrites in the premise of ⊑ such that
    the assumptions P1, P2, ... appear at the front, in that order. *)
Tactic Notation "to_front" open_constr(Ps) :=
  close_uPreds Ps ltac:(fun Ps =>
    uPred_reflection.quote_l;
    let Σ := match goal with |- uPred_reflection.eval ?Σ _ ⊑ _ => Σ end in
    let ns' := lazymatch type of (_ : uPred_reflection.QuoteArgs Σ Ps _) with
               | uPred_reflection.QuoteArgs _ _ ?ns' => ns'
               end in
    eapply entails_equiv_l;
      first (apply uPred_reflection.split_l with (ns:=ns'); cbv; reflexivity);
      simpl).

Tactic Notation "to_back" open_constr(Ps) :=
  close_uPreds Ps ltac:(fun Ps =>
    uPred_reflection.quote_l;
    let Σ := match goal with |- uPred_reflection.eval ?Σ _ ⊑ _ => Σ end in
    let ns' := lazymatch type of (_ : uPred_reflection.QuoteArgs Σ Ps _) with
               | uPred_reflection.QuoteArgs _ _ ?ns' => ns'
               end in
    eapply entails_equiv_l;
      first (apply uPred_reflection.split_r with (ns:=ns'); cbv; reflexivity);
      simpl).

(** [sep_split] is used to introduce a (★).
    Use [sep_split left: [P1, P2, ...]] to define which assertions will be
    taken to the left; the rest will be available on the right.
    [sep_split right: [P1, P2, ...]] works the other way around. *)
Tactic Notation "sep_split" "right:" open_constr(Ps) :=
  to_back Ps; apply sep_mono.
Tactic Notation "sep_split" "left:" open_constr(Ps) :=
  to_front Ps; apply sep_mono.

(** Assumes a goal of the shape P ⊑ ▷ Q. Alterantively, if Q
    is built of ★, ∧, ∨ with ▷ in all branches; that will work, too.
    Will turn this goal into P ⊑ Q and strip ▷ in P below ★, ∧, ∨. *)
Ltac strip_later :=
  let rec strip :=
    lazymatch goal with
    | |- (_ ★ _) ⊑ ▷ _  =>
      etrans; last (eapply equiv_entails_sym, later_sep);
      apply sep_mono; strip
    | |- (_ ∧ _) ⊑ ▷ _  =>
      etrans; last (eapply equiv_entails_sym, later_and);
      apply sep_mono; strip
    | |- (_ ∨ _) ⊑ ▷ _  =>
      etrans; last (eapply equiv_entails_sym, later_or);
      apply sep_mono; strip
    | |- ▷ _ ⊑ ▷ _ => apply later_mono; reflexivity
    | |- _ ⊑ ▷ _ => apply later_intro; reflexivity
    end
  in let rec shape_Q :=
    lazymatch goal with
    | |- _ ⊑ (_ ★ _) =>
      (* Force the later on the LHS to be top-level, matching laters
         below ★ on the RHS *)
      etrans; first (apply equiv_entails, later_sep; reflexivity);
      (* Match the arm recursively *)
      apply sep_mono; shape_Q
    | |- _ ⊑ (_ ∧ _) =>
      etrans; first (apply equiv_entails, later_and; reflexivity);
      apply sep_mono; shape_Q
    | |- _ ⊑ (_ ∨ _) =>
      etrans; first (apply equiv_entails, later_or; reflexivity);
      apply sep_mono; shape_Q
    | |- _ ⊑ ▷ _ => apply later_mono; reflexivity
    (* We fail if we don't find laters in all branches. *)
    end
  in intros_revert ltac:(etrans; [|shape_Q];
                         etrans; last eapply later_mono; first solve [ strip ]).

(** Transforms a goal of the form ∀ ..., ?0... → ?1 ⊑ ?2
    into True ⊑ ∀..., ■?0... → ?1 → ?2, applies tac, and
    the moves all the assumptions back. *)
(* TODO: this name may be a big too general *)
Ltac revert_all :=
  lazymatch goal with
  | |- ∀ _, _ =>
    let H := fresh in intro H; revert_all;
    (* TODO: Really, we should distinguish based on whether this is a
    dependent function type or not. Right now, we distinguish based
    on the sort of the argument, which is suboptimal. *)
    first [ apply (const_intro_impl _ _ _ H); clear H
          | revert H; apply forall_elim']
  | |- _ ⊑ _ => apply impl_entails
  end.

(** This starts on a goal of the form ∀ ..., ?0... → ?1 ⊑ ?2.
   It applies löb where all the Coq assumptions have been turned into logical
   assumptions, then moves all the Coq assumptions back out to the context,
   applies [tac] on the goal (now of the form _ ⊑ _), and then reverts the
   Coq assumption so that we end up with the same shape as where we started,
   but with an additional assumption ★-ed to the context *)
Ltac löb tac :=
  revert_all;
  (* Add a box *)
  etrans; last (eapply always_elim; reflexivity);
  (* We now have a goal for the form True ⊑ P, with the "original" conclusion
     being locked. *)
  apply löb_strong; etransitivity;
    first (apply equiv_entails, left_id, _; reflexivity);
  apply: always_intro;
  (* Now introduce again all the things that we reverted, and at the bottom,
     do the work *)
  let rec go :=
    lazymatch goal with
    | |- _ ⊑ (∀ _, _) =>
      apply forall_intro; let H := fresh in intro H; go; revert H
    | |- _ ⊑ (■ _ → _) =>
      apply impl_intro_l, const_elim_l; let H := fresh in intro H; go; revert H
    (* This is the "bottom" of the goal, where we see the impl introduced
       by uPred_revert_all as well as the ▷ from löb_strong and the □ we added. *)
    | |- ▷ □ ?R ⊑ (?L → _) => apply impl_intro_l;
      trans (L ★ ▷ □ R)%I;
        [eapply equiv_entails, always_and_sep_r, _; reflexivity | tac]
    end
  in go.
