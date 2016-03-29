From iris.algebra Require Export gmap.
From iris.algebra Require Import excl.
From iris.prelude Require Import mapset.

Definition gsetC K `{Countable K} := gmapC K (exclC unitC).

Definition to_gsetC `{Countable K} (X : gset K) : gsetC K :=
  to_gmap (Excl ()) X.

Section gset.
Context `{Countable K}.
Implicit Types X Y : gset K.

Lemma to_gsetC_empty : to_gsetC (∅ : gset K) = ∅.
Proof. apply to_gmap_empty. Qed.
Lemma to_gsetC_union X Y : X ⊥ Y → to_gsetC X ⋅ to_gsetC Y = to_gsetC (X ∪ Y).
Proof.
  intros HXY; apply: map_eq=> i; rewrite /to_gsetC /=.
  rewrite lookup_op !lookup_to_gmap. repeat case_option_guard; set_solver.
Qed.
Lemma to_gsetC_valid X : ✓ to_gsetC X.
Proof. intros i. rewrite /to_gsetC lookup_to_gmap. by case_option_guard. Qed.
Lemma to_gsetC_valid_op X Y : ✓ (to_gsetC X ⋅ to_gsetC Y) ↔ X ⊥ Y.
Proof.
  split; last (intros; rewrite to_gsetC_union //; apply to_gsetC_valid).
  intros HXY i ??; move: (HXY i); rewrite lookup_op !lookup_to_gmap.
  rewrite !option_guard_True //.
Qed.

Context `{Fresh K (gset K), !FreshSpec K (gset K)}.
Lemma updateP_alloc_strong (Q : gsetC K → Prop) (I : gset K) X :
  (∀ i, i ∉ X → i ∉ I → Q (to_gsetC ({[i]} ∪ X))) → to_gsetC X ~~>: Q.
Proof.
  intros; apply updateP_alloc_strong with I (Excl ()); [done|]=> i.
  rewrite /to_gsetC lookup_to_gmap_None -to_gmap_union_singleton; eauto.
Qed.
Lemma updateP_alloc (Q : gsetC K → Prop) X :
  (∀ i, i ∉ X → Q (to_gsetC ({[i]} ∪ X))) → to_gsetC X ~~>: Q.
Proof. move=>??. eapply updateP_alloc_strong with (I:=∅); by eauto. Qed.
Lemma updateP_alloc_strong' (I : gset K) X :
  to_gsetC X ~~>: λ Y : gsetC K, ∃ i, Y = to_gsetC ({[ i ]} ∪ X) ∧ i ∉ I ∧ i ∉ X.
Proof. eauto using updateP_alloc_strong. Qed.
Lemma updateP_alloc' X :
  to_gsetC X ~~>: λ Y : gsetC K, ∃ i, Y = to_gsetC ({[ i ]} ∪ X) ∧ i ∉ X.
Proof. eauto using updateP_alloc. Qed.
End gset.