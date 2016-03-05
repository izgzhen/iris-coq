From heap_lang Require Export derived.
Export heap_lang.

Arguments wp {_ _} _ _%E _.
Notation "#> e @ E {{ Φ } }" := (wp E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "#>  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "#> e {{ Φ } }" := (wp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "#>  e   {{  Φ  } }") : uPred_scope.

Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : binder_scope.
Notation "<>" := BAnon : expr_scope.

(* No scope for the values, does not conflict and scope is often not inferred properly. *)
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l").
Notation "% l" := (LocV l) (at level 8, format "% l").
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l") : val_scope.
Notation "% l" := (LocV l) (at level 8, format "% l") : val_scope.
Notation "# l" := (Lit l%Z%V) (at level 8, format "# l") : expr_scope.
Notation "% l" := (Loc l) (at level 8, format "% l") : expr_scope.

Notation "' x" := (Var x) (at level 8, format "' x") : expr_scope.
Notation "^ v" := (of_val' v%V) (at level 8, format "^ v") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1 e1 x2 e2)
  (e0, x1, e1, x2, e2 at level 200) : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2 e2 x1 e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.
Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E)
  (at level 30, right associativity) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E)
  (at level 35, right associativity) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) (at level 70) : expr_scope.
Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.
Notation "'rec:' f x := e" := (Rec f x e%E)
  (at level 102, f at level 1, x at level 1, e at level 200) : expr_scope.
Notation "'rec:' f x := e" := (RecV f x e%E)
  (at level 102, f at level 1, x at level 1, e at level 200) : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y := e" := (Rec f x (Lam y e%E))
  (at level 102, f, x, y at level 1, e at level 200) : expr_scope.
Notation "'rec:' f x y := e" := (RecV f x (Lam y e%E))
  (at level 102, f, x, y at level 1, e at level 200) : val_scope.
Notation "'rec:' f x y .. z := e" := (Rec f x (Lam y .. (Lam z e%E) ..))
  (at level 102, f, x, y, z at level 1, e at level 200) : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f x (Lam y .. (Lam z e%E) ..))
  (at level 102, f, x, y, z at level 1, e at level 200) : val_scope.

Notation "λ: x , e" := (Lam x  e%E)
  (at level 102, x at level 1, e at level 200) : expr_scope.
Notation "λ: x y .. z , e" := (Lam x (Lam y .. (Lam z e%E) ..))
  (at level 102, x, y, z at level 1, e at level 200) : expr_scope.
Notation "λ: x , e" := (LamV x e%E)
  (at level 102, x at level 1, e at level 200) : val_scope.
Notation "λ: x y .. z , e" := (LamV x (Lam y .. (Lam z e%E) .. ))
  (at level 102, x, y, z at level 1, e at level 200) : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x e2%E e1%E)
  (at level 102, x at level 1, e1, e2 at level 200) : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200, format "e1  ;;  e2") : expr_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" := (LamV x e2%E e1%E)
  (at level 102, x at level 1, e1, e2 at level 200) : val_scope.
Notation "e1 ;; e2" := (LamV BAnon e2%E e1%E)
  (at level 100, e2 at level 200, format "e1  ;;  e2") : val_scope.
