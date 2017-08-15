From iris.proofmode Require Export classes.
From iris.base_logic Require Export base_logic.

(* There are various versions of [IsOp] with different modes:

- [IsOp a b1 b2]: this one has no mode, it can be used regardless of whether
  any of the arguments is an evar. This class has only one direct instance:
  [IsOp (a ⋅ b) a b].
- [IsOp' a b1 b2]: requires either [a] to start with a constructor, OR [b1] and
  [b2] to start with a constructor. All usual instances should be of this
  class to avoid loops.
- [IsOp'LR a b1 b2]: requires either [a] to start with a constructor. This one
  has just one instance: [IsOp'LR (a ⋅ b) a b] with a very low precendence.
  This is important so that when performing, for example, an [iDestruct] on
  [own γ (q1 + q2)] where [q1] and [q2] are fractions, we actually get
  [own γ q1] and [own γ q2] instead of [own γ ((q1 + q2)/2)] twice.
*)
Class IsOp {A : cmraT} (a b1 b2 : A) := is_op : a ≡ b1 ⋅ b2.
Arguments is_op {_} _ _ _ {_}.
Hint Mode IsOp + - - - : typeclass_instances.

Instance is_op_op {A : cmraT} (a b : A) : IsOp (a ⋅ b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : cmraT} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Hint Mode IsOp' + ! - - : typeclass_instances.
Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : cmraT} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Hint Mode IsOp'LR + ! - - : typeclass_instances.
Instance is_op_lr_op {A : cmraT} (a b : A) : IsOp'LR (a ⋅ b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.