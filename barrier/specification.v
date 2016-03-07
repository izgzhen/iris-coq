From program_logic Require Export hoare.
From barrier Require Export barrier.
From barrier Require Import proof.
Import uPred.

Section spec.
Context {Σ : gFunctors} `{!heapG Σ} `{!barrierG Σ}. 

Local Notation iProp := (iPropG heap_lang Σ).

(* TODO: Maybe notation for LocV (and Loc)? *)
Lemma barrier_spec (heapN N : namespace) :
  heapN ⊥ N →
  ∃ recv send : loc → iProp -n> iProp,
    (∀ P, heap_ctx heapN ⊑ {{ True }} newbarrier #() {{ λ v,
                             ∃ l : loc, v = LocV l ★ recv l P ★ send l P }}) ∧
    (∀ l P, {{ send l P ★ P }} signal (LocV l) {{ λ _, True }}) ∧
    (∀ l P, {{ recv l P }} wait (LocV l) {{ λ _, P }}) ∧
    (∀ l P Q, recv l (P ★ Q) ={N}=> recv l P ★ recv l Q) ∧
    (∀ l P Q, (P -★ Q) ⊑ (recv l P -★ recv l Q)).
Proof.
  intros HN.
  exists (λ l, CofeMor (recv heapN N l)), (λ l, CofeMor (send heapN N l)).
  split_and?; simpl.
  - intros P. apply: always_intro. apply impl_intro_r.
    rewrite -(newbarrier_spec heapN N P) // always_and_sep_r.
    apply sep_mono_r, forall_intro=>l; apply wand_intro_l.
    by rewrite right_id -(exist_intro l) const_equiv // left_id.
  - intros l P. apply ht_alt. by rewrite -signal_spec right_id.
  - intros l P. apply ht_alt.
    by rewrite -(wait_spec heapN N l P) wand_diag right_id.
  - intros l P Q. apply vs_alt. rewrite -(recv_split heapN N N l P Q) //.
  - intros l P Q. apply recv_weaken.
Qed.
End spec.
