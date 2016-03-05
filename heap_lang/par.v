From heap_lang Require Export heap.
From heap_lang Require Import spawn notation.

Definition par : val :=
  λ: "f1" "f2", let: "handle" := ^spawn '"f1" in
                let: "v2" := '"f2" #() in
                let: "v1" := ^join '"handle" in
                Pair '"v1" '"v2".
Notation Par e1 e2 := (^par (λ: <>, e1)%V (λ: <>, e2)%V)%E.

Section proof.
Context {Σ : rFunctorG} `{!heapG Σ, !spawnG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Lemma par_spec (Ψ1 Ψ2 : val → iProp) (f1 f2 : val) (Φ : val → iProp) :
  (#> f1 #() {{ Ψ1 }} ★ #> f2 #() {{ Ψ2 }} ★
   ∀ v1 v2, Ψ1 v1 ★ Ψ2 v2 -★ Φ (PairV v1 v2))
  ⊑ #> par f1 f2 {{ Φ }}.
Proof.
Abort.

End proof.