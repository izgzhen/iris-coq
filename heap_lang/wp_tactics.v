From heap_lang Require Export tactics substitution.
Import uPred.

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
  in revert_intros ltac:(etransitivity; [|go]).

Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etransitivity; [|solve [ apply (wp_bind K) ]]; simpl
  end.
Ltac wp_finish :=
  let rec go :=
  match goal with
  | |- _ ⊑ ▷ _ => etransitivity; [|apply later_mono; go; reflexivity]
  | |- _ ⊑ wp _ _ _ =>
     etransitivity; [|eapply wp_value; reflexivity];
     (* sometimes, we will have to do a final view shift, so only apply
     wp_value if we obtain a consecutive wp *)
     match goal with |- _ ⊑ wp _ _ _ => simpl | _ => fail end
  | _ => idtac
  end in simpl; revert_intros go.

Tactic Notation "wp_value" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => etransitivity; [|eapply wp_value; reflexivity]; simpl
  end.
Tactic Notation "wp_rec" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | App (Rec _ _ _) _ =>
       wp_bind K; etransitivity; [|eapply wp_rec; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_rec" := wp_rec>; wp_strip_later.
Tactic Notation "wp_bin_op" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; wp_finish
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; wp_finish
    | BinOp _ _ _ =>
       wp_bind K; etransitivity; [|eapply wp_bin_op; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_bin_op" := wp_bin_op>; wp_strip_later.
Tactic Notation "wp_un_op" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | UnOp _ _ =>
       wp_bind K; etransitivity; [|eapply wp_un_op; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_un_op" := wp_un_op>; wp_strip_later.
Tactic Notation "wp_if" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | If _ _ _ =>
       wp_bind K;
       etransitivity; [|apply wp_if_true || apply wp_if_false]; wp_finish
    end)
  end.
Tactic Notation "wp_if" := wp_if>; wp_strip_later.
Tactic Notation "wp_focus" open_constr(efoc) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with efoc => unify e' efoc; wp_bind K end)
  end.

Tactic Notation "wp" tactic(tac) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' => wp_bind K; tac)
  end.
Tactic Notation "wp" ">" tactic(tac) := (wp tac); wp_strip_later.

(* In case the precondition does not match *)
Tactic Notation "ewp" tactic(tac) := wp (etransitivity; [|tac]).
Tactic Notation "ewp" ">" tactic(tac) := wp> (etransitivity; [|tac]).
