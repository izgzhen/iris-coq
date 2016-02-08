Require Export algebra.base prelude.countable prelude.co_pset.
Require Export program_logic.ownership program_logic.pviewshifts.

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

(** Derived forms and lemmas about them. *)
Definition inv {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  ownI (encode N) P.
(* TODO: Add lemmas about inv here. *)
