Require Export algebra.cofe.

Record solution (F : cofeT → cofeT → cofeT) := Solution {
  solution_car :> cofeT;
  solution_unfold : solution_car -n> F solution_car solution_car;
  solution_fold : F solution_car solution_car -n> solution_car;
  solution_fold_unfold X : solution_fold (solution_unfold X) ≡ X;
  solution_unfold_fold X : solution_unfold (solution_fold X) ≡ X
}.
Arguments solution_unfold {_} _.
Arguments solution_fold {_} _.

Module solver. Section solver.
Context (F : cofeT → cofeT → cofeT).
Context `{Finhab : Inhabited (F unitC unitC)}.
Context (map : ∀ {A1 A2 B1 B2 : cofeT},
  ((A2 -n> A1) * (B1 -n> B2)) → (F A1 B1 -n> F A2 B2)).
Arguments map {_ _ _ _} _.
Instance: Params (@map) 4.
Context (map_id : ∀ {A B : cofeT} (x : F A B), map (cid, cid) x ≡ x).
Context (map_comp : ∀ {A1 A2 A3 B1 B2 B3 : cofeT}
    (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x,
  map (f ◎ g, g' ◎ f') x ≡ map (g,g') (map (f,f') x)).
Context (map_contractive : ∀ {A1 A2 B1 B2}, Contractive (@map A1 A2 B1 B2)).

Lemma map_ext {A1 A2 B1 B2 : cofeT}
  (f : A2 -n> A1) (f' : A2 -n> A1) (g : B1 -n> B2) (g' : B1 -n> B2) x x' :
  (∀ x, f x ≡ f' x) → (∀ y, g y ≡ g' y) → x ≡ x' →
  map (f,g) x ≡ map (f',g') x'.
Proof. by rewrite -!cofe_mor_ext; intros -> -> ->. Qed.

Fixpoint A (k : nat) : cofeT :=
  match k with 0 => unitC | S k => F (A k) (A k) end.
Fixpoint f {k} : A k -n> A (S k) :=
  match k with 0 => CofeMor (λ _, inhabitant) | S k => map (g,f) end
with g {k} : A (S k) -n> A k :=
  match k with 0 => CofeMor (λ _, ()) | S k => map (f,g) end.
Definition f_S k (x : A (S k)) : f x = map (g,f) x := eq_refl.
Definition g_S k (x : A (S (S k))) : g x = map (f,g) x := eq_refl.
Lemma gf {k} (x : A k) : g (f x) ≡ x.
Proof.
  induction k as [|k IH]; simpl in *; [by destruct x|].
  rewrite -map_comp -{2}(map_id _ _ x); by apply map_ext.
Qed.
Lemma fg {n k} (x : A (S k)) : n ≤ k → f (g x) ≡{n}≡ x.
Proof.
  intros Hnk; apply dist_le with k; auto; clear Hnk.
  induction k as [|k IH]; simpl; [apply dist_0|].
  rewrite -{2}(map_id _ _ x) -map_comp; by apply map_contractive.
Qed.
Arguments A _ : simpl never.
Arguments f {_} : simpl never.
Arguments g {_} : simpl never.

Record tower := {
  tower_car k :> A k;
  g_tower k : g (tower_car (S k)) ≡ tower_car k
}.
Instance tower_equiv : Equiv tower := λ X Y, ∀ k, X k ≡ Y k.
Instance tower_dist : Dist tower := λ n X Y, ∀ k, X k ≡{n}≡ Y k.
Program Definition tower_chain (c : chain tower) (k : nat) : chain (A k) :=
  {| chain_car i := c i k |}.
Next Obligation. intros c k n i ?; apply (chain_cauchy c n); lia. Qed.
Program Instance tower_compl : Compl tower := λ c,
  {| tower_car n := compl (tower_chain c n) |}.
Next Obligation.
  intros c k; apply equiv_dist; intros n.
  rewrite (conv_compl (tower_chain c k) n).
  by rewrite (conv_compl (tower_chain c (S k)) n) /= (g_tower (c n) k).
Qed.
Definition tower_cofe_mixin : CofeMixin tower.
Proof.
  split.
  * intros X Y; split; [by intros HXY n k; apply equiv_dist|].
    intros HXY k; apply equiv_dist; intros n; apply HXY.
  * intros k; split.
    + by intros X n.
    + by intros X Y ? n.
    + by intros X Y Z ?? n; transitivity (Y n).
  * intros k X Y HXY n; apply dist_S.
    by rewrite -(g_tower X) (HXY (S n)) g_tower.
  * intros X Y k; apply dist_0.
  * intros c n k; rewrite /= (conv_compl (tower_chain c k) n).
    apply (chain_cauchy c); lia.
Qed.
Definition T : cofeT := CofeT tower_cofe_mixin.

Fixpoint ff {k} (i : nat) : A k -n> A (i + k) :=
  match i with 0 => cid | S i => f ◎ ff i end.
Fixpoint gg {k} (i : nat) : A (i + k) -n> A k :=
  match i with 0 => cid | S i => gg i ◎ g end.
Lemma ggff {k i} (x : A k) : gg i (ff i x) ≡ x.
Proof. induction i as [|i IH]; simpl; [done|by rewrite (gf (ff i x)) IH]. Qed.
Lemma f_tower {n k} (X : tower) : n ≤ k → f (X k) ≡{n}≡ X (S k).
Proof. intros. by rewrite -(fg (X (S k))) // -(g_tower X). Qed.
Lemma ff_tower {n} k i (X : tower) : n ≤ k → ff i (X k) ≡{n}≡ X (i + k).
Proof.
  intros; induction i as [|i IH]; simpl; [done|].
  by rewrite IH (f_tower X); last lia.
Qed.
Lemma gg_tower k i (X : tower) : gg i (X (i + k)) ≡ X k.
Proof. by induction i as [|i IH]; simpl; [done|rewrite g_tower IH]. Qed.

Instance tower_car_ne n k : Proper (dist n ==> dist n) (λ X, tower_car X k).
Proof. by intros X Y HX. Qed.
Definition project (k : nat) : T -n> A k := CofeMor (λ X : T, tower_car X k).

Definition coerce {i j} (H : i = j) : A i -n> A j :=
  eq_rect _ (λ i', A i -n> A i') cid _ H.
Lemma coerce_id {i} (H : i = i) (x : A i) : coerce H x = x.
Proof. unfold coerce. by rewrite (proof_irrel H (eq_refl i)). Qed.
Lemma coerce_proper {i j} (x y : A i) (H1 H2 : i = j) :
  x = y → coerce H1 x = coerce H2 y.
Proof. by destruct H1; rewrite !coerce_id. Qed.
Lemma g_coerce {k j} (H : S k = S j) (x : A (S k)) :
  g (coerce H x) = coerce (Nat.succ_inj _ _ H) (g x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.
Lemma coerce_f {k j} (H : S k = S j) (x : A k) :
  coerce H (f x) = f (coerce (Nat.succ_inj _ _ H) x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.
Lemma gg_gg {k i i1 i2 j} (H1 : k = i + j) (H2 : k = i2 + (i1 + j)) (x : A k) :
  gg i (coerce H1 x) = gg i1 (gg i2 (coerce H2 x)).
Proof.
  assert (i = i2 + i1) by lia; simplify_equality'. revert j x H1.
  induction i2 as [|i2 IH]; intros j X H1; simplify_equality';
    [by rewrite coerce_id|by rewrite g_coerce IH].
Qed.
Lemma ff_ff {k i i1 i2 j} (H1 : i + k = j) (H2 : i1 + (i2 + k) = j) (x : A k) :
  coerce H1 (ff i x) = coerce H2 (ff i1 (ff i2 x)).
Proof.
  assert (i = i1 + i2) by lia; simplify_equality'.
  induction i1 as [|i1 IH]; simplify_equality';
    [by rewrite coerce_id|by rewrite coerce_f IH].
Qed.

Definition embed' {k} (i : nat) : A k -n> A i :=
  match le_lt_dec i k with
  | left H => gg (k-i) ◎ coerce (eq_sym (Nat.sub_add _ _ H))
  | right H => coerce (Nat.sub_add k i (Nat.lt_le_incl _ _ H)) ◎ ff (i-k)
  end.
Lemma g_embed' {k i} (x : A k) : g (embed' (S i) x) ≡ embed' i x.
Proof.
  unfold embed'; destruct (le_lt_dec (S i) k), (le_lt_dec i k); simpl.
  * symmetry; by erewrite (@gg_gg _ _ 1 (k - S i)); simpl.
  * exfalso; lia.
  * assert (i = k) by lia; subst.
    rewrite (ff_ff _ (eq_refl (1 + (0 + k)))) /= gf.
    by rewrite (gg_gg _ (eq_refl (0 + (0 + k)))).
  * assert (H : 1 + ((i - k) + k) = S i) by lia.
    rewrite (ff_ff _ H) /= -{2}(gf (ff (i - k) x)) g_coerce.
    by erewrite coerce_proper by done.
Qed.
Program Definition embed_inf (k : nat) (x : A k) : T :=
  {| tower_car n := embed' n x |}.
Next Obligation. intros k x i. apply g_embed'. Qed.
Instance embed_inf_ne k n : Proper (dist n ==> dist n) (embed_inf k).
Proof. by intros x y Hxy i; rewrite /= Hxy. Qed.
Definition embed (k : nat) : A k -n> T := CofeMor (embed_inf k).
Lemma embed_f k (x : A k) : embed (S k) (f x) ≡ embed k x.
Proof.
  rewrite equiv_dist; intros n i.
  unfold embed_inf, embed; simpl; unfold embed'.
  destruct (le_lt_dec i (S k)), (le_lt_dec i k); simpl.
  * assert (H : S k = S (k - i) + (0 + i)) by lia; rewrite (gg_gg _ H) /=.
    by erewrite g_coerce, gf, coerce_proper by done.
  * assert (S k = 0 + (0 + i)) as H by lia.
    rewrite (gg_gg _ H); simplify_equality'.
    by rewrite (ff_ff _ (eq_refl (1 + (0 + k)))).
  * exfalso; lia.
  * assert (H : (i - S k) + (1 + k) = i) by lia; rewrite (ff_ff _ H) /=.
    by erewrite coerce_proper by done.
Qed.
Lemma embed_tower j n (X : T) : n ≤ j → embed j (X j) ≡{n}≡ X.
Proof.
  move=> Hn i; rewrite /= /embed'; destruct (le_lt_dec i j) as [H|H]; simpl.
  * rewrite -(gg_tower i (j - i) X).
    apply (_ : Proper (_ ==> _) (gg _)); by destruct (eq_sym _).
  * rewrite (ff_tower j (i-j) X); last lia. by destruct (Nat.sub_add _ _ _).
Qed.

Program Definition unfold_chain (X : T) : chain (F T T) :=
  {| chain_car n := map (project n,embed n) (f (X n)) |}.
Next Obligation.
  intros X n i Hi.
  assert (∃ k, i = k + n) as [k ?] by (exists (i - n); lia); subst; clear Hi.
  induction k as [|k Hk]; simpl; [done|].
  rewrite Hk (f_tower X); last lia; rewrite f_S -map_comp.
  apply dist_S, map_contractive.
  split; intros Y; symmetry; apply equiv_dist; [apply g_tower|apply embed_f].
Qed.
Definition unfold (X : T) : F T T := compl (unfold_chain X).
Instance unfold_ne : Proper (dist n ==> dist n) unfold.
Proof. by intros n X Y HXY; apply compl_ne; rewrite /= (HXY n). Qed.

Program Definition fold (X : F T T) : T :=
  {| tower_car n := g (map (embed n,project n) X) |}.
Next Obligation.
  intros X k; apply (_ : Proper ((≡) ==> (≡)) g).
  rewrite -(map_comp _ _ _ _ _ _ (embed (S k)) f (project (S k)) g).
  apply map_ext; [apply embed_f|intros Y; apply g_tower|done].
Qed.
Instance fold_ne : Proper (dist n ==> dist n) fold.
Proof. by intros n X Y HXY k; rewrite /fold /= HXY. Qed.

Theorem result : solution F.
Proof.
  apply (Solution F T (CofeMor unfold) (CofeMor fold)).
  * move=> X.
    assert (map_ff_gg : ∀ i k (x : A (S i + k)) (H : S i + k = i + S k),
      map (ff i, gg i) x ≡ gg i (coerce H x)).
    { intros i; induction i as [|i IH]; intros k x H; simpl.
      { by rewrite coerce_id map_id. }
      rewrite map_comp g_coerce; apply IH. }
    rewrite equiv_dist; intros n k; unfold unfold, fold; simpl.
    rewrite -g_tower -(gg_tower _ n); apply (_ : Proper (_ ==> _) g).
    transitivity (map (ff n, gg n) (X (S (n + k)))).
    { rewrite /unfold (conv_compl (unfold_chain X) n).
      rewrite (chain_cauchy (unfold_chain X) n (n + k)) /=; last lia.
      rewrite (f_tower X); last lia; rewrite -map_comp.
      apply dist_S. apply map_contractive; split; intros x; simpl; unfold embed'.
      * destruct (le_lt_dec _ _); simpl.
        { assert (n = 0) by lia; subst. apply dist_0. }
        by rewrite (ff_ff _ (eq_refl (n + (0 + k)))).
      * destruct (le_lt_dec _ _); [|exfalso; lia]; simpl.
        by rewrite (gg_gg _ (eq_refl (0 + (n + k)))). }
    assert (H: S n + k = n + S k) by lia; rewrite (map_ff_gg _ _ _ H).
    apply (_ : Proper (_ ==> _) (gg _)); by destruct H.
  * move=>X; rewrite equiv_dist=> n.
    rewrite /(unfold) /= /(unfold) (conv_compl (unfold_chain (fold X)) n) /=.
    rewrite (fg (map (embed _,project n) X)); last lia.
    rewrite -map_comp -{2}(map_id _ _ X).
    apply dist_S, map_contractive; split; intros Y i; apply embed_tower; lia.
Qed.
End solver. End solver.
