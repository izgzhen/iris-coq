From iris.prelude Require Import base.

(* Not using [list Type] in order to avoid universe inconsistencies *)
Inductive tlist := tnil : tlist | tcons : Type → tlist → tlist.

Inductive hlist : tlist → Type :=
  | hnil : hlist tnil
  | hcons {A As} : A → hlist As → hlist (tcons A As).

Fixpoint himpl (As : tlist) (B : Type) : Type :=
  match As with tnil => B | tcons A As => A → himpl As B end.

Definition happly {As B} (f : himpl As B) (xs : hlist As) : B :=
  (fix go As xs :=
    match xs in hlist As return himpl As B → B with
    | hnil => λ f, f
    | hcons A As x xs => λ f, go As xs (f x)
    end) _ xs f.
