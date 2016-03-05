From heap_lang Require Export lang.
Import heap_lang.

(** The tactic [simpl_subst] performs substitutions in the goal. Its behavior
can be tuned using instances of the type class [Closed e], which can be used
to mark that expressions are closed, and should thus not be substituted into. *)

(** * Weakening *)
Class WExpr {X Y} (H : X `included` Y) (e : expr X) (er : expr Y) :=
  do_wexpr : wexpr H e = er.
Hint Mode WExpr + + + + - : typeclass_instances.

(* Variables *)
Hint Extern 0 (WExpr _ (Var ?y) _) =>
  apply var_proof_irrel : typeclass_instances.

(* Rec *)
Instance do_wexpr_rec_true {X Y f y e} {H : X `included` Y} er :
  WExpr (wexpr_rec_prf H) e er → WExpr H (Rec f y e) (Rec f y er).
Proof. intros; red; f_equal/=. by etrans; [apply wexpr_proof_irrel|]. Qed.

(* Values *)
Instance do_wexpr_of_val_nil (H : [] `included` []) v :
  WExpr H (of_val v) (of_val v) | 0.
Proof. apply wexpr_id. Qed.
Instance do_wexpr_of_val_nil' X (H : X `included` []) v :
  WExpr H (of_val' v) (of_val v) | 0.
Proof. by rewrite /WExpr /of_val' wexpr_wexpr' wexpr_id. Qed.
Instance do_wexpr_of_val Y (H : [] `included` Y) v :
  WExpr H (of_val v) (of_val' v) | 1.
Proof. apply wexpr_proof_irrel. Qed.
Instance do_wexpr_of_val' X Y (H : X `included` Y) v :
  WExpr H (of_val' v) (of_val' v) | 1.
Proof. apply wexpr_wexpr. Qed.

(* Boring connectives *)
Section do_wexpr.
Context {X Y : list string} (H : X `included` Y).
Notation W := (WExpr H).

(* Ground terms *)
Global Instance do_wexpr_lit l : W (Lit l) (Lit l).
Proof. done. Qed.
Global Instance do_wexpr_loc l : W (Loc l) (Loc l).
Proof. done. Qed.
Global Instance do_wexpr_app e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (App e1 e2) (App e1r e2r).
Proof. intros; red; f_equal/=; apply: do_wexpr. Qed.
Global Instance do_wexpr_unop op e er : W e er → W (UnOp op e) (UnOp op er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_binop op e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (BinOp op e1 e2) (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_if e0 e1 e2 e0r e1r e2r :
  W e0 e0r → W e1 e1r → W e2 e2r → W (If e0 e1 e2) (If e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_pair e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (Pair e1 e2) (Pair e1r e2r).
Proof. by intros ??; red; f_equal/=. Qed.
Global Instance do_wexpr_fst e er : W e er → W (Fst e) (Fst er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_snd e er : W e er → W (Snd e) (Snd er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_injL e er : W e er → W (InjL e) (InjL er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_injR e er : W e er → W (InjR e) (InjR er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_case e0 e1 e2 e0r e1r e2r :
  W e0 e0r → W e1 e1r → W e2 e2r → W (Case e0 e1 e2) (Case e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_fork e er : W e er → W (Fork e) (Fork er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_alloc e er : W e er → W (Alloc e) (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_load e er : W e er → W (Load e) (Load er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_store e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (Store e1 e2) (Store e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_cas e0 e1 e2 e0r e1r e2r :
  W e0 e0r → W e1 e1r → W e2 e2r → W (CAS e0 e1 e2) (CAS e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
End do_wexpr.

(** * WSubstitution *)
Class WSubst {X Y} (x : string) (es : expr []) H (e : expr X) (er : expr Y) :=
  do_wsubst : wsubst x es H e = er.
Hint Mode WSubst + + + + + + - : typeclass_instances.

(* Variables *)
Lemma do_wsubst_var_eq {X Y x es} {H : X `included` x :: Y} `{VarBound x X} er :
  WExpr (included_nil _) es er → WSubst x es H (Var x) er.
Proof.
  intros; red; simpl. case_decide; last done.
  by etrans; [apply wexpr_proof_irrel|].
Qed.
Hint Extern 0 (WSubst ?x ?v _ (Var ?y) _) => first
  [ apply var_proof_irrel
  | apply do_wsubst_var_eq ] : typeclass_instances.

(** Rec *)
Lemma do_wsubst_rec_true {X Y x es f y e} {H : X `included` x :: Y}
    (Hfy : BNamed x ≠ f ∧ BNamed x ≠ y) er :
  WSubst x es (wsubst_rec_true_prf H Hfy) e er →
  WSubst x es H (Rec f y e) (Rec f y er).
Proof.
  intros ?; red; f_equal/=; case_decide; last done.
  by etrans; [apply wsubst_proof_irrel|].
Qed.
Lemma do_wsubst_rec_false {X Y x es f y e} {H : X `included` x :: Y}
    (Hfy : ¬(BNamed x ≠ f ∧ BNamed x ≠ y)) er :
  WExpr (wsubst_rec_false_prf H Hfy) e er →
  WSubst x es H (Rec f y e) (Rec f y er).
Proof.
  intros; red; f_equal/=; case_decide; first done.
  by etrans; [apply wexpr_proof_irrel|].
Qed.

Ltac bool_decide_no_check := apply (bool_decide_unpack _); vm_cast_no_check I.
Hint Extern 0 (WSubst ?x ?v _ (Rec ?f ?y ?e) _) =>
  match eval vm_compute in (bool_decide (BNamed x ≠ f ∧ BNamed x ≠ y)) with
  | true => eapply (do_wsubst_rec_true ltac:(bool_decide_no_check))
  | false => eapply (do_wsubst_rec_false ltac:(bool_decide_no_check))
  end : typeclass_instances.

(* Values *)
Instance do_wsubst_of_val_nil x es (H : [] `included` [x]) w :
  WSubst x es H (of_val w) (of_val w) | 0.
Proof. apply wsubst_closed_nil. Qed.
Instance do_wsubst_of_val_nil' {X} x es (H : X `included` [x]) w :
  WSubst x es H (of_val' w) (of_val w) | 0.
Proof. by rewrite /WSubst /of_val' wsubst_wexpr' wsubst_closed_nil. Qed.
Instance do_wsubst_of_val Y x es (H : [] `included` x :: Y) w :
  WSubst x es H (of_val w) (of_val' w) | 1.
Proof. apply wsubst_closed, not_elem_of_nil. Qed.
Instance do_wsubst_of_val' X Y x es (H : X `included` x :: Y) w :
  WSubst x es H (of_val' w) (of_val' w) | 1.
Proof.
  rewrite /WSubst /of_val' wsubst_wexpr'.
  apply wsubst_closed, not_elem_of_nil.
Qed.

(* Boring connectives *)
Section wsubst.
Context {X Y} (x : string) (es : expr []) (H : X `included` x :: Y).
Notation Sub := (WSubst x es H).

(* Ground terms *)
Global Instance do_wsubst_lit l : Sub (Lit l) (Lit l).
Proof. done. Qed.
Global Instance do_wsubst_loc l : Sub (Loc l) (Loc l).
Proof. done. Qed.
Global Instance do_wsubst_app e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (App e1 e2) (App e1r e2r).
Proof. intros; red; f_equal/=; apply: do_wsubst. Qed.
Global Instance do_wsubst_unop op e er : Sub e er → Sub (UnOp op e) (UnOp op er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_binop op e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (BinOp op e1 e2) (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_if e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (If e0 e1 e2) (If e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_pair e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Pair e1 e2) (Pair e1r e2r).
Proof. by intros ??; red; f_equal/=. Qed.
Global Instance do_wsubst_fst e er : Sub e er → Sub (Fst e) (Fst er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_snd e er : Sub e er → Sub (Snd e) (Snd er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_injL e er : Sub e er → Sub (InjL e) (InjL er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_injR e er : Sub e er → Sub (InjR e) (InjR er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_case e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (Case e0 e1 e2) (Case e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_fork e er : Sub e er → Sub (Fork e) (Fork er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_alloc e er : Sub e er → Sub (Alloc e) (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_load e er : Sub e er → Sub (Load e) (Load er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_store e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Store e1 e2) (Store e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_cas e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (CAS e0 e1 e2) (CAS e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
End wsubst.

(** * The tactic *)
Lemma do_subst {X} (x: string) (es: expr []) (e: expr (x :: X)) (er: expr X) :
  WSubst x es (λ _, id) e er → subst x es e = er.
Proof. done. Qed.

Ltac simpl_subst :=
  repeat match goal with
  | |- context [subst ?x ?es ?e] => progress rewrite (@do_subst _ x es e)
  | |- _ => progress csimpl
  end.
Arguments wexpr : simpl never.
Arguments subst : simpl never.
Arguments wsubst : simpl never.
Arguments of_val : simpl never.
Arguments of_val' : simpl never.
