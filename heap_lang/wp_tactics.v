From heap_lang Require Export tactics substitution.
Import uPred.

Ltac wp_strip_later :=
  match goal with
  | |- ∀ _, _ => let H := fresh in intro H; wp_strip_later; revert H
  | |- _ ⊑ ▷ _ => etransitivity; [|apply later_intro]
  end.
Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etransitivity; [|apply (wp_bind K)]; simpl
  end.
Ltac wp_finish :=
  let rec go :=
  match goal with
  | |- ∀ _, _ => let H := fresh in intro H; go; revert H
  | |- _ ⊑ ▷ _ => etransitivity; [|apply later_mono; go; reflexivity]
  | |- _ ⊑ wp _ _ _ => etransitivity; [|eapply wp_value; reflexivity]; simpl
  | _ => idtac
  end in simpl; go.

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
  try wp_value;
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
