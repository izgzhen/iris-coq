From heap_lang Require Export heap spawn.
From heap_lang Require Import wp_tactics notation.
Import uPred.

Definition par : val :=
  λ: "fs",
    let: "handle" := ^spawn (Fst '"fs") in
    let: "v2" := Snd '"fs" #() in
    let: "v1" := ^join '"handle" in
    Pair '"v1" '"v2".
Notation Par e1 e2 := (^par (Pair (λ: <>, e1) (λ: <>, e2)))%E.
Notation ParV e1 e2 := (par (Pair (λ: <>, e1) (λ: <>, e2)))%E.
(* We want both par and par^ to print like this. *)
Infix "||" := ParV : expr_scope.
Infix "||" := Par : expr_scope.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !spawnG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Lemma par_spec (Ψ1 Ψ2 : val → iProp) e (f1 f2 : val) (Φ : val → iProp) :
  heapN ⊥ N → to_val e = Some (f1,f2)%V →
  (heap_ctx heapN ★ #> f1 #() {{ Ψ1 }} ★ #> f2 #() {{ Ψ2 }} ★
   ∀ v1 v2, Ψ1 v1 ★ Ψ2 v2 -★ ▷ Φ (v1,v2)%V)
  ⊑ #> par e {{ Φ }}.
Proof.
  intros. rewrite /par. ewp (by eapply wp_value). wp_let. wp_proj.
  ewp (eapply spawn_spec; wp_done).
  apply sep_mono_r, sep_mono_r.
  apply forall_intro=>h. apply wand_intro_l. wp_let. wp_proj.
  wp_focus (f2 _). rewrite wp_frame_r wp_frame_l. apply wp_mono=>v2. wp_let.
  ewp (by eapply join_spec).
  apply sep_mono_r, forall_intro=>v1; apply wand_intro_l.
  rewrite (forall_elim v1) (forall_elim v2). rewrite assoc wand_elim_r.
  wp_let. apply wp_value; wp_done.
Qed.

Lemma wp_par (Ψ1 Ψ2 : val → iProp) (e1 e2 : expr []) (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ #> e1 {{ Ψ1 }} ★ #> e2 {{ Ψ2 }} ★
   ∀ v1 v2, Ψ1 v1 ★ Ψ2 v2 -★ ▷ Φ (v1,v2)%V)
  ⊑ #> ParV e1 e2 {{ Φ }}.
Proof.
  intros. rewrite -par_spec //. repeat apply sep_mono; done || by wp_seq.
Qed.
End proof.
