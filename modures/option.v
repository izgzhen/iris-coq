Require Export modures.cmra.

(* COFE *)
Section cofe.
Context {A : cofeT}.
Inductive option_dist : Dist (option A) :=
  | option_0_dist (x y : option A) : x ={0}= y
  | Some_dist n x y : x ={n}= y → Some x ={n}= Some y
  | None_dist n : None ={n}= None.
Existing Instance option_dist.
Program Definition option_chain
    (c : chain (option A)) (x : A) (H : c 1 = Some x) : chain A :=
  {| chain_car n := from_option x (c n) |}.
Next Obligation.
  intros c x ? n i ?; simpl; destruct (decide (i = 0)) as [->|].
  { by replace n with 0 by lia. }
  feed inversion (chain_cauchy c 1 i); auto with lia congruence.
  feed inversion (chain_cauchy c n i); simpl; auto with lia congruence.
Qed.
Instance option_compl : Compl (option A) := λ c,
  match Some_dec (c 1) with
  | inleft (exist x H) => Some (compl (option_chain c x H)) | inright _ => None
  end.
Definition option_cofe_mixin : CofeMixin (option A).
Proof.
  split.
  * intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
    intros Hxy; feed inversion (Hxy 1); subst; constructor; apply equiv_dist.
    by intros n; feed inversion (Hxy n).
  * intros n; split.
    + by intros [x|]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
  * by inversion_clear 1; constructor; apply dist_S.
  * constructor.
  * intros c n; unfold compl, option_compl.
    destruct (decide (n = 0)) as [->|]; [constructor|].
    destruct (Some_dec (c 1)) as [[x Hx]|].
    { assert (is_Some (c n)) as [y Hy].
      { feed inversion (chain_cauchy c 1 n); try congruence; eauto with lia. }
      rewrite Hy; constructor.
      by rewrite (conv_compl (option_chain c x Hx) n); simpl; rewrite Hy. }
    feed inversion (chain_cauchy c 1 n); auto with lia congruence; constructor.
Qed.
Canonical Structure optionC := CofeT option_cofe_mixin.
Global Instance Some_ne : Proper (dist n ==> dist n) (@Some A).
Proof. by constructor. Qed.
Global Instance None_timeless : Timeless (@None A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance Some_timeless x : Timeless x → Timeless (Some x).
Proof. by intros ?; inversion_clear 1; constructor; apply timeless. Qed.
End cofe.

Arguments optionC : clear implicits.

Instance option_fmap_ne {A B : cofeT} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n==>dist n) (fmap (M:=option) f).
Proof. by intros Hf; destruct 1; constructor; apply Hf. Qed.
Instance is_Some_ne `{A : cofeT} : Proper (dist (S n) ==> iff) (@is_Some A).
Proof. intros n; inversion_clear 1; split; eauto. Qed.

(* CMRA *)
Section cmra.
Context {A : cmraT}.

Instance option_valid : Valid (option A) := λ mx,
  match mx with Some x => ✓ x | None => True end.
Instance option_validN : ValidN (option A) := λ n mx,
  match mx with Some x => ✓{n} x | None => True end.
Instance option_unit : Unit (option A) := fmap unit.
Instance option_op : Op (option A) := union_with (λ x y, Some (x ⋅ y)).
Instance option_minus : Minus (option A) :=
  difference_with (λ x y, Some (x ⩪ y)).
Lemma option_included mx my :
  mx ≼ my ↔ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼ y.
Proof.
  split.
  * intros [mz Hmz]; destruct mx as [x|]; [right|by left].
    destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
    destruct mz as [z|]; inversion_clear Hmz; split_ands; auto;
      setoid_subst; eauto using ra_included_l.
  * intros [->|(x&y&->&->&z&Hz)]; try (by exists my; destruct my; constructor).
    by exists (Some z); constructor.
Qed.
Lemma option_includedN n (mx my : option A) :
  mx ≼{n} my ↔ n = 0 ∨ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼{n} y.
Proof.
  split.
  * intros [mz Hmz]; destruct n as [|n]; [by left|right].
    destruct mx as [x|]; [right|by left].
    destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
    destruct mz as [z|]; inversion_clear Hmz; split_ands; auto;
      cofe_subst; eauto using @cmra_included_l.
  * intros [->|[->|(x&y&->&->&z&Hz)]];
      try (by exists my; destruct my; constructor).
    by exists (Some z); constructor.
Qed.
Definition option_cmra_mixin  : CMRAMixin (option A).
Proof.
  split.
  * by intros n [x|]; destruct 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * by destruct 1; constructor; apply (_ : Proper (dist n ==> _) _).
  * destruct 1 as [[?|] [?|]| |]; unfold validN, option_validN; simpl;
     intros ?; auto using cmra_valid_0;
     eapply (_ : Proper (dist _ ==> impl) (✓{_})); eauto.
  * by destruct 1; inversion_clear 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * intros [x|]; unfold validN, option_validN; auto using cmra_valid_0.
  * intros n [x|]; unfold validN, option_validN; eauto using @cmra_valid_S.
  * by intros [x|]; unfold valid, validN, option_validN, option_valid;
      eauto using cmra_valid_validN.
  * intros [x|] [y|] [z|]; constructor; rewrite ?(associative _); auto.
  * intros [x|] [y|]; constructor; rewrite 1?(commutative _); auto.
  * by intros [x|]; constructor; rewrite ra_unit_l.
  * by intros [x|]; constructor; rewrite ra_unit_idempotent.
  * intros n mx my; rewrite !option_includedN;intros [|[->|(x&y&->&->&?)]];auto.
    do 2 right; exists (unit x), (unit y); eauto using @cmra_unit_preserving.
  * intros n [x|] [y|]; unfold validN, option_validN; simpl;
      eauto using @cmra_valid_op_l.
  * intros n mx my; rewrite option_includedN.
    intros [->|[->|(x&y&->&->&?)]]; [done|by destruct my|].
    by constructor; apply cmra_op_minus.
Qed.
Definition option_cmra_extend_mixin : CMRAExtendMixin (option A).
Proof.
  intros n mx my1 my2; destruct (decide (n = 0)) as [->|].
  { by exists (mx, None); repeat constructor; destruct mx; constructor. }
  destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
    try (by exfalso; inversion Hx'; auto).
  * destruct (cmra_extend_op n x y1 y2) as ([z1 z2]&?&?&?); auto.
    { by inversion_clear Hx'. }
    by exists (Some z1, Some z2); repeat constructor.
  * by exists (Some x,None); inversion Hx'; repeat constructor.
  * by exists (None,Some x); inversion Hx'; repeat constructor.
  * exists (None,None); repeat constructor.
Qed.
Canonical Structure optionRA :=
  CMRAT option_cofe_mixin option_cmra_mixin option_cmra_extend_mixin.

Lemma option_op_positive_dist_l n x y : x ⋅ y ={n}= None → x ={n}= None.
Proof. by destruct x, y; inversion_clear 1. Qed.
Lemma option_op_positive_dist_r n x y : x ⋅ y ={n}= None → y ={n}= None.
Proof. by destruct x, y; inversion_clear 1. Qed.
End cmra.

Arguments optionRA : clear implicits.

Instance option_fmap_cmra_monotone {A B : cmraT} (f: A → B) `{!CMRAMonotone f} :
  CMRAMonotone (fmap f : option A → option B).
Proof.
  split.
  * intros n mx my; rewrite !option_includedN.
    intros [->|[->|(x&y&->&->&?)]]; simpl; eauto 10 using @includedN_preserving.
  * by intros n [x|] ?; rewrite /cmra_validN /=; try apply validN_preserving.
Qed.
