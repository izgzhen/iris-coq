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

Instance ndot_inj `{Countable A} : Inj2 (=) (=) (=) (@ndot A _ _).
Proof. by intros N1 x1 N2 x2 ?; simplify_equality. Qed.
Lemma nclose_nnil : nclose nnil = coPset_all.
Proof. by apply (sig_eq_pi _). Qed.
Lemma encode_nclose N : encode N ∈ nclose N.
Proof. by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _). Qed.
Lemma nclose_subseteq `{Countable A} N x : nclose (ndot N x) ⊆ nclose N.
Proof.
  intros p; rewrite /nclose !elem_coPset_suffixes; intros [q ->].
  destruct (list_encode_suffix N (ndot N x)) as [q' ?]; [by exists [encode x]|].
  by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
Qed.
Lemma ndot_nclose `{Countable A} N x : encode (ndot N x) ∈ nclose N.
Proof. apply nclose_subseteq with x, encode_nclose. Qed.
Lemma nclose_disjoint `{Countable A} N (x y : A) :
  x ≠ y → nclose (ndot N x) ∩ nclose (ndot N y) = ∅.
Proof.
  intros Hxy; apply elem_of_equiv_empty_L=> p; unfold nclose, ndot.
  rewrite elem_of_intersection !elem_coPset_suffixes; intros [[q ->] [q' Hq]].
  apply Hxy, (inj encode), (inj encode_nat); revert Hq.
  rewrite !(list_encode_cons (encode _)).
  rewrite !(assoc_L _) (inj_iff (++ _)%positive) /=.
  generalize (encode_nat (encode y)).
  induction (encode_nat (encode x)); intros [|?] ?; f_equal'; naive_solver.
Qed.

Local Hint Resolve nclose_subseteq ndot_nclose.

(** Derived forms and lemmas about them. *)
Definition inv {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  (∃ i, ■ (i ∈ nclose N) ∧ ownI i P)%I.
Instance: Params (@inv) 3.
Typeclasses Opaque inv.

Section inv.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.

Global Instance inv_contractive N : Contractive (@inv Λ Σ N).
Proof. intros n ???. apply exists_ne=>i. by apply and_ne, ownI_contractive. Qed.

Global Instance inv_always_stable N P : AlwaysStable (inv N P).
Proof. rewrite /inv; apply _. Qed.

Lemma always_inv N P : (□ inv N P)%I ≡ inv N P.
Proof. by rewrite always_always. Qed.

(** Invariants can be opened around any frame-shifting assertion. *)
Lemma inv_fsa {A : Type} {FSA} (FSAs : FrameShiftAssertion (A:=A) FSA)
      E N P (Q : A → iProp Λ Σ) :
  nclose N ⊆ E →
  (inv N P ★ (▷P -★ FSA (E ∖ nclose N) (λ a, ▷P ★ Q a))) ⊑ FSA E Q.
Proof.
  move=>HN.
  rewrite /inv sep_exist_r. apply exist_elim=>i.
  rewrite always_and_sep_l' -assoc. apply const_elim_sep_l=>HiN.
  rewrite -(fsa_trans3 E (E ∖ {[encode i]})) //; last by solve_elem_of+.
  (* Add this to the local context, so that solve_elem_of finds it. *)
  assert ({[encode i]} ⊆ nclose N) by eauto.
  rewrite (always_sep_dup' (ownI _ _)).
  rewrite {1}pvs_openI !pvs_frame_r.
  apply pvs_mask_frame_mono ; [solve_elem_of..|].
  rewrite (comm _ (▷_)%I) -assoc wand_elim_r fsa_frame_l.
  apply fsa_mask_frame_mono; [solve_elem_of..|]. intros a.
  rewrite assoc -always_and_sep_l' pvs_closeI pvs_frame_r left_id.
  apply pvs_mask_frame'; solve_elem_of.
Qed.

(* Derive the concrete forms for pvs and wp, because they are useful. *)

Lemma pvs_open_close E N P Q :
  nclose N ⊆ E →
  (inv N P ★ (▷P -★ pvs (E ∖ nclose N) (E ∖ nclose N) (▷P ★ Q))) ⊑ pvs E E Q.
Proof. move=>HN. by rewrite (inv_fsa pvs_fsa). Qed.

Lemma wp_open_close E e N P (Q : val Λ → iProp Λ Σ) :
  atomic e → nclose N ⊆ E →
  (inv N P ★ (▷P -★ wp (E ∖ nclose N) e (λ v, ▷P ★ Q v))) ⊑ wp E e Q.
Proof.
  move=>He HN. by rewrite (inv_fsa (wp_fsa e _)). Qed.

Lemma inv_alloc N P : ▷ P ⊑ pvs N N (inv N P).
Proof. by rewrite /inv (pvs_allocI N); last apply coPset_suffixes_infinite. Qed.

End inv.
