From algebra Require Export base.
From prelude Require Export countable co_pset.
From program_logic Require Import ownership.
From program_logic Require Export pviewshifts weakestpre.
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

Definition ndisj (N1 N2 : namespace) :=
  ∃ N1' N2', N1' `suffix_of` N1 ∧ N2' `suffix_of` N2 ∧
             length N1' = length N2' ∧ N1' ≠ N2'.

Global Instance ndisj_comm : Comm iff ndisj.
Proof. intros N1 N2. rewrite /ndisj; naive_solver. Qed.

Lemma ndot_ne_disj `{Countable A} N (x y : A) :
  x ≠ y → ndisj (ndot N x) (ndot N y).
Proof.
  intros Hxy. exists (ndot N x), (ndot N y). split_ands; try done; [].
  by apply not_inj2_2.
Qed.

Lemma ndot_preserve_disj_l `{Countable A} N1 N2 (x : A) :
  ndisj N1 N2 → ndisj (ndot N1 x) N2.
Proof.
  intros (N1' & N2' & Hpr1 & Hpr2 & Hl & Hne). exists N1', N2'.
  split_ands; try done; []. by apply suffix_of_cons_r.
Qed.

Lemma ndot_preserve_disj_r `{Countable A} N1 N2 (x : A) :
  ndisj N1 N2 → ndisj N1 (ndot N2 x).
Proof.
  rewrite ![ndisj N1 _]comm. apply ndot_preserve_disj_l.
Qed.

Lemma ndisj_disjoint N1 N2 :
  ndisj N1 N2 → nclose N1 ∩ nclose N2 = ∅.
Proof.
  intros (N1' & N2' & [N1'' Hpr1] & [N2'' Hpr2] & Hl & Hne). subst N1 N2.
  apply elem_of_equiv_empty_L=> p; unfold nclose.
  rewrite elem_of_intersection !elem_coPset_suffixes; intros [[q ->] [q' Hq]].
  rewrite !list_encode_app !assoc in Hq.
  apply Hne. eapply list_encode_suffix_eq; done.
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
Lemma inv_fsa {A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa}
    E N P (Q : A → iProp Λ Σ) R :
  fsaV →
  nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷ P -★ fsa (E ∖ nclose N) (λ a, ▷ P ★ Q a)) →
  R ⊑ fsa E Q.
Proof.
  intros ? HN Hinv Hinner.
  rewrite -[R](idemp (∧)%I) {1}Hinv Hinner =>{Hinv Hinner R}.
  rewrite always_and_sep_l /inv sep_exist_r. apply exist_elim=>i.
  rewrite always_and_sep_l -assoc. apply const_elim_sep_l=>HiN.
  rewrite -(fsa_open_close E (E ∖ {[encode i]})) //; last by solve_elem_of+.
  (* Add this to the local context, so that solve_elem_of finds it. *)
  assert ({[encode i]} ⊆ nclose N) by eauto.
  rewrite (always_sep_dup (ownI _ _)).
  rewrite {1}pvs_openI !pvs_frame_r.
  apply pvs_mask_frame_mono; [solve_elem_of..|].
  rewrite (comm _ (▷_)%I) -assoc wand_elim_r fsa_frame_l.
  apply fsa_mask_frame_mono; [solve_elem_of..|]. intros a.
  rewrite assoc -always_and_sep_l pvs_closeI pvs_frame_r left_id.
  apply pvs_mask_frame'; solve_elem_of.
Qed.

(* Derive the concrete forms for pvs and wp, because they are useful. *)

Lemma pvs_open_close E N P Q R :
  nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷P -★ pvs (E ∖ nclose N) (E ∖ nclose N) (▷P ★ Q)) →
  R ⊑ pvs E E Q.
Proof. intros. by apply: (inv_fsa pvs_fsa). Qed.

Lemma wp_open_close E e N P (Q : val Λ → iProp Λ Σ) R :
  atomic e → nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷P -★ wp (E ∖ nclose N) e (λ v, ▷P ★ Q v)) →
  R ⊑ wp E e Q.
Proof. intros. by apply: (inv_fsa (wp_fsa e)). Qed.

Lemma inv_alloc N P : ▷ P ⊑ pvs N N (inv N P).
Proof. by rewrite /inv (pvs_allocI N); last apply coPset_suffixes_infinite. Qed.

End inv.
