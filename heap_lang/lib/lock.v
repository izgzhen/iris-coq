From iris.heap_lang Require Import heap notation.

Structure lock Σ `{!heapG Σ} := Lock {
  (* -- operations -- *)
  newlock : val;
  acquire : val;
  release : val;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  name : Type;
  is_lock (N: namespace) (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (* -- general properties -- *)
  is_lock_ne N γ lk n: Proper (dist n ==> dist n) (is_lock N γ lk);
  is_lock_persistent N γ lk R : PersistentP (is_lock N γ lk R);
  locked_timeless γ : TimelessP (locked γ);
  locked_exclusive γ : locked γ ★ locked γ ⊢ False;
  (* -- operation specs -- *)
  newlock_spec N (R : iProp Σ) Φ :
    heapN ⊥ N →
    heap_ctx ★ R ★ (∀ l γ, is_lock N γ l R -★ Φ l) ⊢ WP newlock #() {{ Φ }};
  acquire_spec N γ lk R (Φ : val → iProp Σ) :
    is_lock N γ lk R ★ (locked γ -★ R -★ Φ #()) ⊢ WP acquire lk {{ Φ }};
  release_spec N γ lk R (Φ : val → iProp Σ) :
    is_lock N γ lk R ★ locked γ ★ R ★ Φ #() ⊢ WP release lk {{ Φ }}
}.

Arguments newlock {_ _} _.
Arguments acquire {_ _} _.
Arguments release {_ _} _.
Arguments is_lock {_ _} _ _ _ _ _.
Arguments locked {_ _} _ _.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper Σ `{!heapG Σ} (L: lock Σ) N lk R:
  Proper ((≡) ==> (≡)) (is_lock L N lk R) := ne_proper _.

