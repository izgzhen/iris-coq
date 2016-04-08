From iris.algebra Require Export upred_tactics.
From iris.heap_lang Require Export tactics derived substitution.
Import uPred.

(** wp-specific helper tactics *)
Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

Ltac wp_finish :=
  intros_revert ltac:(
    try strip_later;
    match goal with
    | |- _ ⊢ wp _ _ _ =>
      etrans; [|eapply wp_value_pvs; fast_done]; lazy beta;
      (* sometimes, we will have to do a final view shift, so only apply
      pvs_intro if we obtain a consecutive wp *)
      try (etrans; [|apply pvs_intro];
           match goal with |- _ ⊢ wp _ _ _ => simpl | _ => fail end)
    | _ => idtac
    end).

Ltac wp_done := rewrite -/of_val /= ?to_of_val; fast_done.

Tactic Notation "wp_rec" :=
  löb ltac:(
    (* Find the redex and apply wp_rec *)
    idtac; (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4584> *)
    lazymatch goal with
    | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
      match eval hnf in e' with App ?e1 _ =>
(* hnf does not reduce through an of_val *)
(*      match eval hnf in e1 with Rec _ _ _ => *)
      wp_bind K; etrans; [|eapply wp_rec'; wp_done]; simpl_subst; wp_finish
(*      end *) end)
     end).

Tactic Notation "wp_lam" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(*    match eval hnf in e1 with Rec BAnon _ _ => *)
    wp_bind K; etrans; [|eapply wp_lam; wp_done]; simpl_subst; wp_finish
(*    end *) end)
  end.

Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; wp_finish
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; wp_finish
    | BinOp _ _ _ =>
       wp_bind K; etrans; [|eapply wp_bin_op; try fast_done]; wp_finish
    | UnOp _ _ =>
       wp_bind K; etrans; [|eapply wp_un_op; try fast_done]; wp_finish
    end)
  end.

Tactic Notation "wp_proj" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Fst _ => wp_bind K; etrans; [|eapply wp_fst; wp_done]; wp_finish
    | Snd _ => wp_bind K; etrans; [|eapply wp_snd; wp_done]; wp_finish
    end)
  end.

Tactic Notation "wp_if" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with If _ _ _ =>
    wp_bind K;
    etrans; [|eapply wp_if_true || eapply wp_if_false]; wp_finish
    end)
  end.

Tactic Notation "wp_case" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with Case _ _ _ =>
      wp_bind K;
      etrans; [|first[eapply wp_case_inl; wp_done|eapply wp_case_inr; wp_done]];
      wp_finish
    end)
  end.

Tactic Notation "wp_focus" open_constr(efoc) :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with efoc => unify e' efoc; wp_bind K end)
  end.

Tactic Notation "wp" tactic(tac) :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind K; tac; [try strip_later|..])
  end.

(* In case the precondition does not match.
   TODO: Have one tactic unifying wp and ewp. *)
Tactic Notation "ewp" tactic(tac) := wp (etrans; [|tac]).
