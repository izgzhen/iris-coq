From heap_lang Require Export derived.

Arguments wp {_ _} _ _%L _.
Notation "|| e @ E {{ Φ } }" := (wp E e%L Φ)
  (at level 20, e, Φ at level 200,
   format "||  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "|| e {{ Φ } }" := (wp ⊤ e%L Φ)
  (at level 20, e, Φ at level 200,
   format "||  e   {{  Φ  } }") : uPred_scope.

Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
(** No coercion from base_lit to expr. This makes is slightly easier to tell
   apart language and Coq expressions. *)
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : binder_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)

(* No scope, does not conflict and scope is often not inferred properly. *)
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l").
Notation "% l" := (LocV l) (at level 8, format "% l").

Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : lang_scope.
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1 e1 x2 e2)
  (e0, x1, e1, x2, e2 at level 200) : lang_scope.
Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%L) (at level 9, right associativity) : lang_scope.
Notation "'ref' e" := (Alloc e%L)
  (at level 30, right associativity) : lang_scope.
Notation "- e" := (UnOp MinusUnOp e%L)
  (at level 35, right associativity) : lang_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%L e2%L)
  (at level 50, left associativity) : lang_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%L e2%L)
  (at level 50, left associativity) : lang_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%L e2%L) (at level 70) : lang_scope.
Notation "e1 < e2" := (BinOp LtOp e1%L e2%L) (at level 70) : lang_scope.
Notation "e1 = e2" := (BinOp EqOp e1%L e2%L) (at level 70) : lang_scope.
Notation "~ e" := (UnOp NegOp e%L) (at level 75, right associativity) : lang_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%L e2%L) (at level 80) : lang_scope.
Notation "'rec:' f x := e" := (Rec f x e%L)
  (at level 102, f at level 1, x at level 1, e at level 200) : lang_scope.
Notation "'rec:' f x := e" := (RecV f x e%L)
  (at level 102, f at level 1, x at level 1, e at level 200) : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%L e2%L e3%L)
  (at level 200, e1, e2, e3 at level 200) : lang_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "λ: x , e" := (Lam x e%L)
  (at level 102, x at level 1, e at level 200) : lang_scope.
Notation "λ: x , e" := (LamV x e%L)
  (at level 102, x at level 1, e at level 200) : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x e2%L e1%L)
  (at level 102, x at level 1, e1, e2 at level 200) : lang_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%L e1%L)
  (at level 100, e2 at level 200, format "e1  ;;  e2") : lang_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" := (LamV x e2%L e1%L)
  (at level 102, x at level 1, e1, e2 at level 200) : val_scope.
Notation "e1 ;; e2" := (LamV BAnon e2%L e1%L)
  (at level 100, e2 at level 200, format "e1  ;;  e2") : val_scope.

Notation "'rec:' f x y := e" := (Rec f x (Lam y e%L))
  (at level 102, f, x, y at level 1, e at level 200) : lang_scope.
Notation "'rec:' f x y := e" := (RecV f x (Lam y e%L))
  (at level 102, f, x, y at level 1, e at level 200) : val_scope.
Notation "'rec:' f x y z := e" := (Rec f x (Lam y (Lam z e%L)))
  (at level 102, f, x, y, z at level 1, e at level 200) : lang_scope.
Notation "'rec:' f x y z := e" := (RecV f x (Lam y (Lam z e%L)))
  (at level 102, f, x, y, z at level 1, e at level 200) : val_scope.
Notation "λ: x y , e" := (Lam x (Lam y e%L))
  (at level 102, x, y at level 1, e at level 200) : lang_scope.
Notation "λ: x y , e" := (LamV x (Lam y e%L))
  (at level 102, x, y at level 1, e at level 200) : val_scope.
Notation "λ: x y z , e" := (Lam x (Lam y (Lam z e%L)))
  (at level 102, x, y, z at level 1, e at level 200) : lang_scope.
Notation "λ: x y z , e" := (LamV x (Lam y (Lam z e%L)))
  (at level 102, x, y, z at level 1, e at level 200) : val_scope.
