Require Export algebra.base prelude.countable prelude.co_pset.
Require Import program_logic.ownership.
Require Export program_logic.pviewshifts program_logic.weakestpre.
Import uPred.

Local Hint Extern 100 (@eq coPset _ _) => solve_elem_of.
Local Hint Extern 100 (@subseteq coPset _ _) => solve_elem_of.
Local Hint Extern 100 (_ ∉ _) => solve_elem_of.
Local Hint Extern 99 ({[ _ ]} ⊆ _) => apply elem_of_subseteq_singleton.

Definition namespace := list positive.
Definition nnil : namespace := nil.
Definition ndot `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Coercion nclose (N : namespace) : coPset := coPset_suffixes (encode N).

Instance ndot_injective `{Countable A} : Injective2 (=) (=) (=) (@ndot A _ _).
Proof. by intros N1 x1 N2 x2 ?; simplify_equality. Qed.
Lemma nclose_nnil : nclose nnil = coPset_all.
Proof. by apply (sig_eq_pi _). Qed.
Lemma encode_nclose N : encode N ∈ nclose N.
Proof. by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _). Qed.
Lemma nclose_subseteq `{Countable A} N x : nclose (ndot N x) ⊆ nclose N.
Proof.
  intros p; rewrite /nclose !elem_coPset_suffixes; intros [q ->].
  destruct (list_encode_suffix N (ndot N x)) as [q' ?]; [by exists [encode x]|].
  by exists (q ++ q')%positive; rewrite <-(associative_L _); f_equal.
Qed.
Lemma ndot_nclose `{Countable A} N x : encode (ndot N x) ∈ nclose N.
Proof. apply nclose_subseteq with x, encode_nclose. Qed.
Lemma nclose_disjoint `{Countable A} N (x y : A) :
  x ≠ y → nclose (ndot N x) ∩ nclose (ndot N y) = ∅.
Proof.
  intros Hxy; apply elem_of_equiv_empty_L=> p; unfold nclose, ndot.
  rewrite elem_of_intersection !elem_coPset_suffixes; intros [[q ->] [q' Hq]].
  apply Hxy, (injective encode), (injective encode_nat); revert Hq.
  rewrite !(list_encode_cons (encode _)).
  rewrite !(associative_L _) (injective_iff (++ _)%positive) /=.
  generalize (encode_nat (encode y)).
  induction (encode_nat (encode x)); intros [|?] ?; f_equal'; naive_solver.
Qed.

Local Hint Resolve nclose_subseteq ndot_nclose.

(** Derived forms and lemmas about them. *)
Definition inv {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  (∃ i : positive, ■(i ∈ nclose N) ∧ ownI i P)%I.

Section inv.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.

Global Instance inv_contractive N : Contractive (@inv Λ Σ N).
Proof.
  intros n ? ? EQ. apply exists_ne=>i.
  apply and_ne; first done.
  by apply ownI_contractive.
Qed.

Global Instance inv_always_stable N P : AlwaysStable (inv N P) := _.

Lemma always_inv N P : (□ inv N P)%I ≡ inv N P.
Proof. by rewrite always_always. Qed.

(* We actually pretty much lose the abolity to deal with mask-changing view
   shifts when using `inv`. This is because we cannot exactly name the invariants
   any more. But that's okay; all this means is that sugar like the atomic
   triples will have to prove its own version of the open_close rule
   by unfolding `inv`. *)
(* TODO Can we prove something that helps for both open_close lemmas? *)
Lemma pvs_open_close E N P Q :
  nclose N ⊆ E →
  (inv N P ∧ (▷P -★ pvs (E ∖ nclose N) (E ∖ nclose N) (▷P ★ Q))) ⊑ pvs E E Q.
Proof.
  move=>HN.
  rewrite /inv and_exist_r. apply exist_elim=>i.
  rewrite -associative. apply const_elim_l=>HiN.
  rewrite -(pvs_trans3 E (E ∖ {[encode i]})) //; last by solve_elem_of+.
  (* Add this to the local context, so that solve_elem_of finds it. *)
  assert ({[encode i]} ⊆ nclose N) by eauto.
  rewrite always_and_sep_l' (always_sep_dup' (ownI _ _)).
  rewrite {1}pvs_openI !pvs_frame_r.
  apply pvs_mask_frame_mono ; [solve_elem_of..|].
  rewrite (commutative _ (▷_)%I) -associative wand_elim_r pvs_frame_l.
  apply pvs_mask_frame_mono; [solve_elem_of..|].
  rewrite associative -always_and_sep_l' pvs_closeI pvs_frame_r left_id.
  apply pvs_mask_frame'; solve_elem_of.
Qed.

Lemma wp_open_close E e N P (Q : val Λ → iProp Λ Σ) :
  atomic e → nclose N ⊆ E →
  (inv N P ∧ (▷P -★ wp (E ∖ nclose N) e (λ v, ▷P ★ Q v)))%I ⊑ wp E e Q.
Proof.
  move=>He HN.
  rewrite /inv and_exist_r. apply exist_elim=>i.
  rewrite -associative. apply const_elim_l=>HiN.
  rewrite -(wp_atomic E (E ∖ {[encode i]})) //; last by solve_elem_of+.
  (* Add this to the local context, so that solve_elem_of finds it. *)
  assert ({[encode i]} ⊆ nclose N) by eauto.
  rewrite always_and_sep_l' (always_sep_dup' (ownI _ _)).
  rewrite {1}pvs_openI !pvs_frame_r.
  apply pvs_mask_frame_mono; [solve_elem_of..|].
  rewrite (commutative _ (▷_)%I) -associative wand_elim_r wp_frame_l.
  apply wp_mask_frame_mono; [solve_elem_of..|]=>v.
  rewrite associative -always_and_sep_l' pvs_closeI pvs_frame_r left_id.
  apply pvs_mask_frame'; solve_elem_of.
Qed.

Lemma pvs_alloc N P : ▷ P ⊑ pvs N N (inv N P).
Proof.
  rewrite /inv (pvs_allocI N); first done.
  apply coPset_suffixes_infinite.
Qed.

End inv.
