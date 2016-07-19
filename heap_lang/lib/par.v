From iris.heap_lang Require Export spawn.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition par : val :=
  λ: "fs",
    let: "handle" := spawn (Fst "fs") in
    let: "v2" := Snd "fs" #() in
    let: "v1" := join "handle" in
    Pair "v1" "v2".
Notation Par e1 e2 := (par (Pair (λ: <>, e1) (λ: <>, e2)))%E.
Infix "||" := Par : expr_scope.
Global Opaque par.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !spawnG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Lemma par_spec (Ψ1 Ψ2 : val → iProp) e (f1 f2 : val) (Φ : val → iProp) :
  heapN ⊥ N → to_val e = Some (f1,f2)%V →
  (heap_ctx heapN ★ WP f1 #() {{ Ψ1 }} ★ WP f2 #() {{ Ψ2 }} ★
   ∀ v1 v2, Ψ1 v1 ★ Ψ2 v2 -★ ▷ Φ (v1,v2)%V)
  ⊢ WP par e {{ Φ }}.
Proof.
  iIntros (??) "(#Hh&Hf1&Hf2&HΦ)".
  rewrite /par. wp_value. iPvsIntro. wp_let. wp_proj.
  wp_apply spawn_spec; try wp_done. iFrame "Hf1 Hh".
  iIntros (l) "Hl". wp_let. wp_proj. wp_focus (f2 _).
  iApply wp_wand_l; iFrame "Hf2"; iIntros (v) "H2". wp_let.
  wp_apply join_spec; iFrame "Hl". iIntros (w) "H1".
  iSpecialize ("HΦ" with "* [-]"); first by iSplitL "H1". by wp_let.
Qed.

Lemma wp_par (Ψ1 Ψ2 : val → iProp)
    (e1 e2 : expr) `{!Closed [] e1, Closed [] e2} (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ WP e1 {{ Ψ1 }} ★ WP e2 {{ Ψ2 }} ★
   ∀ v1 v2, Ψ1 v1 ★ Ψ2 v2 -★ ▷ Φ (v1,v2)%V)
  ⊢ WP e1 || e2 {{ Φ }}.
Proof.
  iIntros (?) "(#Hh&H1&H2&H)". iApply (par_spec Ψ1 Ψ2); try wp_done.
  iFrame "Hh H". iSplitL "H1"; by wp_let.
Qed.
End proof.
