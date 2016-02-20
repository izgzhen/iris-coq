From heap_lang Require Export tactics substitution.
Import uPred.

(* TODO: The next 6 tactics are not wp-specific at all. They should move elsewhere. *)

Ltac revert_intros tac :=
  lazymatch goal with
  | |- ∀ _, _ => let H := fresh in intro H; revert_intros tac; revert H
  | |- _ => tac
  end.
Ltac wp_strip_later :=
  let rec go :=
    lazymatch goal with
    | |- _ ⊑ (_ ★ _) => apply sep_mono; go
    | |- _ ⊑ ▷ _ => apply later_intro
    | |- _ ⊑ _ => reflexivity
    end
  in revert_intros ltac:(etrans; [|go]).

(** Assumes a goal of the shape P ⊑ ▷ Q.
    Will get rid of ▷ in P below ★, ∧ and ∨. *)
Ltac u_strip_later :=
  let rec strip :=
      match goal with
      | |- (_ ★ _) ⊑ ▷ _  =>
        etrans; last (eapply equiv_spec, later_sep);
        apply sep_mono; strip
      | |- (_ ∧ _) ⊑ ▷ _  =>
        etrans; last (eapply equiv_spec, later_and);
        apply sep_mono; strip
      | |- (_ ∨ _) ⊑ ▷ _  =>
        etrans; last (eapply equiv_spec, later_or);
        apply sep_mono; strip
      | |- ▷ _ ⊑ ▷ _ => apply later_mono; reflexivity
      | |- _ ⊑ ▷ _ => apply later_intro; reflexivity
      end
  in etrans; last eapply later_mono; first solve [ strip ].

(* ssreflect-locks the part after the ⊑ *)
(* FIXME: I tried doing a lazymatch to only apply the tactic if the goal has shape ⊑,
   bit the match is executed *before* doing the recursion... WTF? *)
Ltac u_lock_goal := revert_intros ltac:(apply uPred_lock_conclusion).

(** Transforms a goal of the form ∀ ..., ?0... → ?1 ⊑ ?2
    into True ⊑ ∀..., ■?0... → ?1 → ?2, applies tac, and
    the moves all the assumptions back. *)
Ltac u_revert_all :=
  lazymatch goal with
  | |- ∀ _, _ => let H := fresh in intro H; u_revert_all;
                 (* TODO: Really, we should distinguish based on whether this is a
                    dependent function type or not. Right now, we distinguish based
                    on the sort of the argument, which is suboptimal. *)
                 first [ apply (const_intro_impl _ _ _ H); clear H
                       | revert H; apply forall_elim']
  | |- ?C ⊑ _ => trans (True ★ C)%I;
                 first (rewrite [(True ★ C)%I]left_id; reflexivity);
                 apply wand_elim_l'
  end.

(** This starts on a goal of the form ∀ ..., ?0... → ?1 ⊑ ?2.
   It applies löb where all the Coq assumptions have been turned into logical
   assumptions, then moves all the Coq assumptions back out to the context,
   applies [tac] on the goal (now of the form _ ⊑ _), and then reverts the Coq
   assumption so that we end up with the same shape as where we started. *)
Ltac u_löb tac :=
  u_lock_goal; u_revert_all;
  (* We now have a goal for the form True ⊑ P, with the "original" conclusion
     being locked. *)
  apply löb_strong; etransitivity;
    first (apply equiv_spec; symmetry; apply (left_id _ _ _); reflexivity);
  (* Now introduce again all the things that we reverted, and at the bottom, do the work *)
  let rec go :=
      lazymatch goal with
      | |- _ ⊑ (∀ _, _) => apply forall_intro;
               let H := fresh in intro H; go; revert H
      | |- _ ⊑ (■ _ → _) => apply impl_intro_l, const_elim_l;
               let H := fresh in intro H; go; revert H
      | |- ▷ ?R ⊑ (?L -★ locked _) => apply wand_intro_l;
               (* TODO: Do sth. more robust than rewriting. *)
               trans (▷ L ★ ▷ R)%I; first (apply sep_mono_l, later_intro; reflexivity);
               trans (▷ (L ★ R))%I; first (apply equiv_spec, later_sep; reflexivity );
               unlock; tac
      end
  in go.

Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|solve [ apply (wp_bind K) ]]; simpl
  end.
Ltac wp_finish :=
  let rec go :=
  match goal with
  | |- _ ⊑ ▷ _ => etrans; [|apply later_mono; go; reflexivity]
  | |- _ ⊑ wp _ _ _ =>
     etrans; [|eapply wp_value_pvs; reflexivity];
     (* sometimes, we will have to do a final view shift, so only apply
     wp_value if we obtain a consecutive wp *)
     try (eapply pvs_intro;
          match goal with |- _ ⊑ wp _ _ _ => simpl | _ => fail end)
  | _ => idtac
  end in simpl; revert_intros go.

Tactic Notation "wp_rec" :=
  u_löb ltac:((* Find the redex and apply wp_rec *)
               match goal with
               | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
                        match eval cbv in e' with
                        | App (Rec _ _ _) _ =>
                          wp_bind K; etrans; [|eapply wp_rec; reflexivity]; wp_finish
                        end)
               end;
               apply later_mono).

Tactic Notation "wp_lam" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | App (Rec "" _ _) _ =>
       wp_bind K; etrans; [|eapply wp_lam; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_lam" := wp_lam>; wp_strip_later.

Tactic Notation "wp_let" ">" := wp_lam>.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" ">" := wp_let>.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; wp_finish
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; wp_finish
    | BinOp _ _ _ =>
       wp_bind K; etrans; [|eapply wp_bin_op; reflexivity]; wp_finish
    | UnOp _ _ =>
       wp_bind K; etrans; [|eapply wp_un_op; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_op" := wp_op>; wp_strip_later.

Tactic Notation "wp_if" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | If _ _ _ =>
       wp_bind K;
       etrans; [|apply wp_if_true || apply wp_if_false]; wp_finish
    end)
  end.
Tactic Notation "wp_if" := wp_if>; wp_strip_later.

Tactic Notation "wp_focus" open_constr(efoc) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with efoc => unify e' efoc; wp_bind K end)
  end.

Tactic Notation "wp" ">" tactic(tac) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' => wp_bind K; tac)
  end.
Tactic Notation "wp" tactic(tac) := (wp> tac); [wp_strip_later|..].

(* In case the precondition does not match *)
Tactic Notation "ewp" tactic(tac) := wp (etrans; [|tac]).
Tactic Notation "ewp" ">" tactic(tac) := wp> (etrans; [|tac]).
