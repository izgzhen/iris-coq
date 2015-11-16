Require Export iris.cmra iris.cofe_maps.
Require Import prelude.pmap prelude.nmap prelude.zmap.
Require Import prelude.stringmap prelude.natmap.

(** option *)
Instance option_valid `{Valid A} : Valid (option A) := λ x,
  match x with Some x => valid x | None => True end.
Instance option_validN `{ValidN A} : ValidN (option A) := λ n x,
  match x with Some x => validN n x | None => True end.
Instance option_unit `{Unit A} : Unit (option A) := fmap unit.
Instance option_op `{Op A} : Op (option A) := union_with (λ x y, Some (x ⋅ y)).
Instance option_minus `{Minus A} : Minus (option A) :=
  difference_with (λ x y, Some (x ⩪ y)).
Inductive option_included `{Included A} : Included (option A) :=
  | Some_included x y : x ≼ y → Some x ≼ Some y
  | None_included x : None ≼ x.
Existing Instance option_included.
Instance option_cmra `{CMRA A} : CMRA (option A).
Proof.
  split.
  * apply _.
  * by intros n [x|]; destruct 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * by destruct 1; constructor; apply (_ : Proper (dist n ==> _) _).
  * destruct 1 as [[?|] [?|]| |]; unfold validN, option_validN; simpl;
     intros ?; auto using cmra_valid_0;
     eapply (_ : Proper (dist _ ==> impl) (validN _)); eauto.
  * by destruct 1; inversion_clear 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * intros [x|]; destruct 1; inversion_clear 1; constructor;
      eapply (_ : Proper (equiv ==> impl) (included _)); eauto.
  * intros [x|]; unfold validN, option_validN; auto using cmra_valid_0.
  * intros n [x|]; unfold validN, option_validN; auto using cmra_valid_S.
  * by intros [x|]; unfold valid, validN, option_validN, option_valid;
      auto using cmra_valid_validN.
  * intros [x|] [y|] [z|]; constructor; rewrite ?(associative _); auto.
  * intros [x|] [y|]; constructor; rewrite 1?(commutative _); auto.
  * by intros [x|]; constructor; rewrite cmra_unit_l.
  * by intros [x|]; constructor; rewrite cmra_unit_idempotent.
  * intros [x|] [y|]; constructor; auto using cmra_unit_weaken.
  * intros n [x|] [y|]; unfold validN, option_validN; simpl;
      eauto using cmra_valid_op_l.
  * intros [x|] [y|]; constructor; auto using cmra_included_l.
  * destruct 1 as [|[]]; constructor; eauto using cmra_op_minus.
Qed.
Instance option_cmra_extend `{CMRA A, !CMRAExtend A} : CMRAExtend (option A).
Proof.
  intros mx my1 my2 n; destruct (decide (n = 0)) as [->|].
  { by exists (mx, None); repeat constructor; destruct mx; constructor. }
  destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
    try (by exfalso; inversion Hx'; auto).
  * destruct (cmra_extend_op x y1 y2 n) as ([z1 z2]&?&?&?); auto.
    { by inversion_clear Hx'. }
    by exists (Some z1, Some z2); repeat constructor.
  * by exists (Some x,None); inversion Hx'; repeat constructor.
  * by exists (None,Some x); inversion Hx'; repeat constructor.
  * exists (None,None); repeat constructor.
Qed.

(** fin maps *)
Section map.
  Context `{FinMap K M}.
  Existing Instances map_dist map_compl map_cofe.
  Instance map_op `{Op A} : Op (M A) := merge op.
  Instance map_unit `{Unit A} : Unit (M A) := fmap unit.
  Instance map_valid `{Valid A} : Valid (M A) := λ m, ∀ i, valid (m !! i).
  Instance map_validN `{ValidN A} : ValidN (M A) := λ n m, ∀ i, validN n (m!!i).
  Instance map_minus `{Minus A} : Minus (M A) := merge minus.
  Instance map_included `{Included A} : Included (M A) := λ m1 m2,
    ∀ i, m1 !! i ≼ m2 !! i.
  Lemma lookup_op `{Op A} m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
  Proof. by apply lookup_merge. Qed.
  Lemma lookup_minus `{Minus A} m1 m2 i : (m1 ⩪ m2) !! i = m1 !! i ⩪ m2 !! i.
  Proof. by apply lookup_merge. Qed.
  Lemma lookup_unit `{Unit A} m i : unit m !! i = unit (m !! i).
  Proof. by apply lookup_fmap. Qed.
  Instance map_cmra `{CMRA A} : CMRA (M A).
  Proof.
    split.
    * apply _.
    * by intros n m1 m2 m3 Hm i; rewrite !lookup_op, (Hm i).
    * by intros n m1 m2 Hm i; rewrite !lookup_unit, (Hm i).
    * by intros n m1 m2 Hm ? i; rewrite <-(Hm i).
    * intros n m1 m1' Hm1 m2 m2' Hm2 i.
      by rewrite !lookup_minus, (Hm1 i), (Hm2 i).
    * by intros m1 m2 m2' Hm2 ? i; rewrite <-(Hm2 i).
    * intros m i; apply cmra_valid_0.
    * intros n m Hm i; apply cmra_valid_S, Hm.
    * intros m; split; [by intros Hm n i; apply cmra_valid_validN|].
      intros Hm i; apply cmra_valid_validN; intros n; apply Hm.
    * by intros m1 m2 m3 i; rewrite !lookup_op, (associative _).
    * by intros m1 m2 i; rewrite !lookup_op, (commutative _).
    * by intros m i; rewrite lookup_op, !lookup_unit, ra_unit_l.
    * by intros m i; rewrite !lookup_unit, ra_unit_idempotent.
    * intros m1 m2 i; rewrite !lookup_unit, lookup_op; apply ra_unit_weaken.
    * intros n m1 m2 Hm i; apply cmra_valid_op_l with (m2 !! i).
      by rewrite <-lookup_op.
    * intros m1 m2 i; rewrite lookup_op; apply ra_included_l.
    * by intros m1 m2 Hm i; rewrite lookup_op, lookup_minus, ra_op_minus.
  Qed.
  Instance map_ra_empty `{RA A} : RAEmpty (M A).
  Proof.
    split.
    * by intros ?; rewrite lookup_empty.
    * by intros m i; simpl; rewrite lookup_op, lookup_empty; destruct (m !! i).
  Qed.
  Instance map_cmra_extend `{CMRA A, !CMRAExtend A} : CMRAExtend (M A).
  Proof.
    intros m m1 m2 n Hm Hm12.
    assert (∀ i, m !! i ={n}= m1 !! i ⋅ m2 !! i) as Hm12'
      by (by intros i; rewrite <-lookup_op).
    set (f i := cmra_extend_op (m !! i) (m1 !! i) (m2 !! i) n (Hm i) (Hm12' i)).
    set (f_proj i := proj1_sig (f i)).
    exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
      repeat split; simpl; intros i; rewrite ?lookup_op, !lookup_imap.
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [|constructor].
      rewrite <-Hx; apply (proj2_sig (f i)).
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
  Qed.
  Definition mapRA (A : cmraT) : cmraT := CMRAT (M A).
End map.

Arguments mapRA {_} _ {_ _ _ _ _ _ _ _ _} _.

Canonical Structure natmapRA := mapRA natmap.
Canonical Structure PmapRA := mapRA Pmap.
Canonical Structure NmapRA := mapRA Nmap.
Canonical Structure ZmapRA := mapRA Zmap.
Canonical Structure stringmapRA := mapRA stringmap.
