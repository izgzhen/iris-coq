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

Tactic Notation "wp_value" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => etransitivity; [|by eapply wp_value]; simpl
  end.
Tactic Notation "wp_rec" "!" :=
  repeat wp_value;
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | App (Rec _ _ _) _ => wp_bind K; etransitivity; [|by eapply wp_rec]; simpl
    end)
  end.
Tactic Notation "wp_rec" := wp_rec!; wp_strip_later.
Tactic Notation "wp_bin_op" "!" :=
  repeat wp_value;
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; [|]
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; [|]
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; [|]
    | BinOp _ _ _ => wp_bind K; etransitivity; [|by eapply wp_bin_op]; simpl
    end)
  end.

Tactic Notation "wp_bin_op" := wp_bin_op!; wp_strip_later.
Tactic Notation "wp_un_op" "!" :=
  repeat wp_value;
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | UnOp _ _ => wp_bind K; etransitivity; [|by eapply wp_un_op]; simpl
    end)
  end.
Tactic Notation "wp_un_op" := wp_un_op!; wp_strip_later.
Tactic Notation "wp_if" "!" :=
  repeat wp_value;
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | If _ _ _ =>
       wp_bind K; etransitivity; [|by apply wp_if_true || by apply wp_if_false]
    end)
  end.
Tactic Notation "wp_if" := wp_if!; wp_strip_later.
Tactic Notation "wp_focus" open_constr(efoc) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with efoc => unify e' efoc; wp_bind K end)
  end.
