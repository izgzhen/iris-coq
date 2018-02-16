From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics classes.
From iris.bi.lib Require Import atomic.
Set Default Proof Using "Type".

Definition atomic_wp `{irisG Λ Σ} {A B : Type}
  (e: expr Λ) (* expression *)
  (α: A → iProp Σ) (* atomic pre-condition *)
  (β: A → B → iProp Σ) (* atomic post-condition *)
  (Ei Eo: coPset) (* inside/outside masks *)
  (f: A → B → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    (∀ Φ, atomic_shift α β Ei Eo (λ x y, Φ (f x y)) -∗
          WP e {{ Φ }})%I.
