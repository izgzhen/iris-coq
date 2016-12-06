From iris.heap_lang Require Export spawn.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition parN : namespace := nroot .@ "par".

Definition par : val :=
  locked (λ: "fs",
    let: "handle" := spawn (Fst "fs") in
    let: "v2" := Snd "fs" #() in
    let: "v1" := join "handle" in
    ("v1", "v2"))%V.
Notation "e1 ||| e2" := (par (Pair (λ: <>, e1) (λ: <>, e2)))%E : expr_scope.

Section proof.
Context `{!heapG Σ, !spawnG Σ}.

(* Notice that this allows us to strip a later *after* the two Ψ have been
   brought together.  That is strictly stronger than first stripping a later
   and then merging them, as demonstrated by [tests/joining_existentials.v].
   This is why these are not Texan triples. *)
Lemma par_spec (Ψ1 Ψ2 : val → iProp Σ) e (f1 f2 : val) (Φ : val → iProp Σ) :
  to_val e = Some (f1,f2)%V →
  (heap_ctx ∗ WP f1 #() {{ Ψ1 }} ∗ WP f2 #() {{ Ψ2 }} ∗
   ▷ ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V)
  ⊢ WP par e {{ Φ }}.
Proof.
  iIntros (?) "(#Hh&Hf1&Hf2&HΦ)".
  rewrite /par -lock. wp_value. wp_let. wp_proj.
  wp_apply (spawn_spec parN with "[$Hh $Hf1]"); try wp_done; try solve_ndisj.
  iIntros (l) "Hl". wp_let. wp_proj. wp_bind (f2 _).
  iApply (wp_wand with "Hf2"); iIntros (v) "H2". wp_let.
  wp_apply (join_spec with "[$Hl]"). iIntros (w) "H1".
  iSpecialize ("HΦ" with "* [-]"); first by iSplitL "H1". by wp_let.
Qed.

Lemma wp_par (Ψ1 Ψ2 : val → iProp Σ)
    (e1 e2 : expr) `{!Closed [] e1, Closed [] e2} (Φ : val → iProp Σ) :
  (heap_ctx ∗ WP e1 {{ Ψ1 }} ∗ WP e2 {{ Ψ2 }} ∗
   ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V)
  ⊢ WP e1 ||| e2 {{ Φ }}.
Proof.
  iIntros "(#Hh&H1&H2&H)". iApply (par_spec Ψ1 Ψ2 with "[- $Hh $H]"); try wp_done.
  iSplitL "H1"; by wp_let.
Qed.
End proof.

Global Opaque par.
