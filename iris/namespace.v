Require Export prelude.countable prelude.co_pset.

Definition namespace := list positive.
Definition nnil : namespace := nil.
Definition ndot `{Countable A} (I : namespace) (x : A) : namespace :=
  encode x :: I.
Definition nclose (I : namespace) : coPset := coPset_suffixes (encode I).

Instance ndot_injective `{Countable A} : Injective2 (=) (=) (=) (@ndot A _ _).
Proof. by intros I1 x1 I2 x2 ?; simplify_equality. Qed.
Lemma nclose_nnil : nclose nnil = coPset_all.
Proof. by apply (sig_eq_pi _). Qed.
Lemma encode_nclose I : encode I ∈ nclose I.
Proof. by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _). Qed.
Lemma nclose_subseteq `{Countable A} I x : nclose (ndot I x) ⊆ nclose I.
Proof.
  intros p; unfold nclose; rewrite !elem_coPset_suffixes; intros [q ->].
  destruct (list_encode_suffix I (ndot I x)) as [q' ?]; [by exists [encode x]|].
  by exists (q ++ q')%positive; rewrite <-(associative_L _); f_equal.
Qed.
Lemma ndot_nclose `{Countable A} I x : encode (ndot I x) ∈ nclose I.
Proof. apply nclose_subseteq with x, encode_nclose. Qed.
Lemma nclose_disjoint `{Countable A} I (x y : A) :
  x ≠ y → nclose (ndot I x) ∩ nclose (ndot I y) = ∅.
Proof.
  intros Hxy; apply elem_of_equiv_empty_L; intros p; unfold nclose, ndot.
  rewrite elem_of_intersection, !elem_coPset_suffixes; intros [[q ->] [q' Hq]].
  apply Hxy, (injective encode), (injective encode_nat); revert Hq.
  rewrite !(list_encode_cons (encode _)).
  rewrite !(associative_L _), (injective_iff (++ _)%positive); simpl.
  generalize (encode_nat (encode y)).
  induction (encode_nat (encode x)); intros [|?] ?; f_equal'; naive_solver.
Qed.