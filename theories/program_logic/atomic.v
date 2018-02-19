From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics classes.
From iris.bi.lib Require Export atomic.
Set Default Proof Using "Type".

Definition atomic_wp `{irisG Λ Σ} {A B : Type}
  (e: expr Λ) (* expression *)
  (α: A → iProp Σ) (* atomic pre-condition *)
  (β: A → B → iProp Σ) (* atomic post-condition *)
  (Eo Em : coPset) (* outside/module masks *)
  (f: A → B → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    (∀ Φ, atomic_update α β Eo Em (λ x y, Φ (f x y)) -∗
          WP e {{ Φ }})%I.
(* Note: To add a private postcondition, use
   atomic_update α β Eo Em (λ x y, POST x y -∗ Φ (f x y)) *)
