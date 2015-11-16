Require Export prelude.prelude.
Obligation Tactic := idtac.

(** Unbundeled version *)
Class Dist A := dist : nat → relation A.
Instance: Params (@dist) 3.
Notation "x ={ n }= y" := (dist n x y)
  (at level 70, n at next level, format "x  ={ n }=  y").
Hint Extern 0 (?x ={_}= ?x) => reflexivity.
Hint Extern 0 (_ ={_}= _) => symmetry; assumption.

Record chain (A : Type) `{Dist A} := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car n ={n}= chain_car i
}.
Arguments chain_car {_ _} _ _.
Arguments chain_cauchy {_ _} _ _ _ _.
Class Compl A `{Dist A} := compl : chain A → A.

Class Cofe A `{Equiv A, Compl A} := {
  equiv_dist x y : x ≡ y ↔ ∀ n, x ={n}= y;
  dist_equivalence n :> Equivalence (dist n);
  dist_S n x y : x ={S n}= y → x ={n}= y;
  dist_0 x y : x ={0}= y;
  conv_compl (c : chain A) n : compl c ={n}= c n
}.
Hint Extern 0 (_ ={0}= _) => apply dist_0.
Class Contractive `{Dist A, Dist B} (f : A -> B) :=
  contractive n : Proper (dist n ==> dist (S n)) f.

(** Bundeled version *)
Structure cofeT := CofeT {
  cofe_car :> Type;
  cofe_equiv : Equiv cofe_car;
  cofe_dist : Dist cofe_car;
  cofe_compl : Compl cofe_car;
  cofe_cofe : Cofe cofe_car
}.
Arguments CofeT _ {_ _ _ _}.
Add Printing Constructor cofeT.
Existing Instances cofe_equiv cofe_dist cofe_compl cofe_cofe.

(** General properties *)
Section cofe.
  Context `{Cofe A}.
  Global Instance cofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    * by intros x; rewrite equiv_dist.
    * by intros x y; rewrite !equiv_dist.
    * by intros x y z; rewrite !equiv_dist; intros; transitivity y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (dist n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    * by transitivity x1; [done|]; transitivity y1.
    * by transitivity x2; [done|]; transitivity y2.
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (dist n).
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    by rewrite equiv_dist in Hx, Hy; rewrite (Hx n), (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Lemma dist_le x y n n' : x ={n}= y → n' ≤ n → x ={n'}= y.
  Proof. induction 2; eauto using dist_S. Qed.
  Instance ne_proper `{Cofe B} (f : A → B)
    `{!∀ n, Proper (dist n ==> dist n) f} : Proper ((≡) ==> (≡)) f | 100.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Instance ne_proper_2 `{Cofe B, Cofe C} (f : A → B → C)
    `{!∀ n, Proper (dist n ==> dist n ==> dist n) f} :
    Proper ((≡) ==> (≡) ==> (≡)) f | 100.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite Hx, Hy.
  Qed.
  Lemma compl_ne (c1 c2: chain A) n : c1 n ={n}= c2 n → compl c1 ={n}= compl c2.
  Proof. intros. by rewrite (conv_compl c1 n), (conv_compl c2 n). Qed.
  Lemma compl_ext (c1 c2 : chain A) : (∀ i, c1 i ≡ c2 i) → compl c1 ≡ compl c2.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using compl_ne. Qed.
  Global Instance contractive_ne `{Cofe B} (f : A → B) `{!Contractive f} n :
    Proper (dist n ==> dist n) f | 100.
  Proof. by intros x1 x2 ?; apply dist_S, contractive. Qed.
  Global Instance contractive_proper `{Cofe B} (f : A → B) `{!Contractive f} :
    Proper ((≡) ==> (≡)) f | 100 := _.
End cofe.

(** Fixpoint *)
Program Definition fixpoint_chain `{Cofe A} (f : A → A) `{!Contractive f}
  (x : A) : chain A := {| chain_car i := Nat.iter i f x |}.
Next Obligation.
  intros A ???? f ? x n; induction n as [|n IH]; intros i ?; [done|].
  destruct i as [|i]; simpl; try lia; apply contractive, IH; auto with lia.
Qed.
Program Definition fixpoint `{Cofe A} (f : A → A) `{!Contractive f}
  (x : A) : A := compl (fixpoint_chain f x).

Section fixpoint.
  Context `{Cofe A} (f : A → A) `{!Contractive f}.
  Lemma fixpoint_unfold x : fixpoint f x ≡ f (fixpoint f x).
  Proof.
    apply equiv_dist; intros n; unfold fixpoint.
    rewrite (conv_compl (fixpoint_chain f x) n).
    by rewrite (chain_cauchy (fixpoint_chain f x) n (S n)) at 1 by lia.
  Qed.
  Lemma fixpoint_ne (g : A → A) `{!Contractive g} x y n :
    (∀ z, f z ={n}= g z) → fixpoint f x ={n}= fixpoint g y.
  Proof.
    intros Hfg; unfold fixpoint; rewrite (conv_compl (fixpoint_chain f x) n),
      (conv_compl (fixpoint_chain g y) n).
    induction n as [|n IH]; simpl in *; [done|].
    rewrite Hfg; apply contractive, IH; auto using dist_S.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} x :
    (∀ x, f x ≡ g x) → fixpoint f x ≡ fixpoint g x.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.
End fixpoint.

(** Function space *)
Structure cofeMor (A B : cofeT) : Type := CofeMor {
  cofe_mor_car :> A → B;
  cofe_mor_ne n : Proper (dist n ==> dist n) cofe_mor_car
}.
Arguments CofeMor {_ _} _ {_}.
Add Printing Constructor cofeMor.
Existing Instance cofe_mor_ne.

Instance cofe_mor_proper `(f : cofeMor A B) : Proper ((≡) ==> (≡)) f := _.
Instance cofe_mor_equiv {A B : cofeT} : Equiv (cofeMor A B) := λ f g,
  ∀ x, f x ≡ g x.
Instance cofe_mor_dist (A B : cofeT) : Dist (cofeMor A B) := λ n f g,
  ∀ x, f x ={n}= g x.
Program Definition fun_chain `(c : chain (cofeMor A B)) (x : A) : chain B :=
  {| chain_car n := c n x |}.
Next Obligation. intros A B c x n i ?. by apply (chain_cauchy c). Qed.
Program Instance cofe_mor_compl (A B : cofeT) : Compl (cofeMor A B) := λ c,
  {| cofe_mor_car x := compl (fun_chain c x) |}.
Next Obligation.
  intros A B c n x y Hxy.
  rewrite (conv_compl (fun_chain c x) n), (conv_compl (fun_chain c y) n).
  simpl; rewrite Hxy; apply (chain_cauchy c); lia.
Qed.
Instance cofe_mor_cofe (A B : cofeT) : Cofe (cofeMor A B).
Proof.
  split.
  * intros X Y; split; [intros HXY n k; apply equiv_dist, HXY|].
    intros HXY k; apply equiv_dist; intros n; apply HXY.
  * intros n; split.
    + by intros f x.
    + by intros f g ? x.
    + by intros f g h ?? x; transitivity (g x).
  * by intros n f g ? x; apply dist_S.
  * by intros f g x.
  * intros c n x; simpl.
    rewrite (conv_compl (fun_chain c x) n); apply (chain_cauchy c); lia.
Qed.
Instance cofe_mor_car_ne A B n :
  Proper (dist n ==> dist n ==> dist n) (@cofe_mor_car A B).
Proof. intros f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
Instance cofe_mor_car_proper A B :
  Proper ((≡) ==> (≡) ==> (≡)) (@cofe_mor_car A B) := ne_proper_2 _.
Lemma cofe_mor_ext {A B} (f g : cofeMor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
Proof. done. Qed.
Canonical Structure cofe_mor (A B : cofeT) : cofeT := CofeT (cofeMor A B).
Infix "-n>" := cofe_mor (at level 45, right associativity).

(** Identity and composition *)
Definition cid {A} : A -n> A := CofeMor id.
Instance: Params (@cid) 1.
Definition ccompose {A B C}
  (f : B -n> C) (g : A -n> B) : A -n> C := CofeMor (f ∘ g).
Instance: Params (@ccompose) 3.
Infix "◎" := ccompose (at level 40, left associativity).
Lemma ccompose_ne {A B C} (f1 f2 : B -n> C) (g1 g2 : A -n> B) n :
  f1 ={n}= f2 → g1 ={n}= g2 → f1 ◎ g1 ={n}= f2 ◎ g2.
Proof. by intros Hf Hg x; simpl; rewrite (Hg x), (Hf (g2 x)). Qed.

(** Pre-composition as a functor *)
Local Instance ccompose_l_ne' {A B C} (f : B -n> A) n :
  Proper (dist n ==> dist n) (λ g : A -n> C, g ◎ f).
Proof. by intros g1 g2 ?; apply ccompose_ne. Qed.
Definition ccompose_l {A B C} (f : B -n> A) : (A -n> C) -n> (B -n> C) :=
  CofeMor (λ g : A -n> C, g ◎ f).
Instance ccompose_l_ne {A B C} : Proper (dist n ==> dist n) (@ccompose_l A B C).
Proof. by intros n f1 f2 Hf g x; apply ccompose_ne. Qed.

(** unit *)
Instance unit_dist : Dist unit := λ _ _ _, True.
Instance unit_compl : Compl unit := λ _, ().
Instance unit_cofe : Cofe unit.
Proof. by repeat split; try exists 0. Qed.

(** Product *)
Instance prod_dist `{Dist A, Dist B} : Dist (A * B) := λ n,
  prod_relation (dist n) (dist n).
Program Definition fst_chain `{Dist A, Dist B} (c : chain (A * B)) : chain A :=
  {| chain_car n := fst (c n) |}.
Next Obligation. by intros A ? B ? c n i ?; apply (chain_cauchy c n). Qed.
Program Definition snd_chain `{Dist A, Dist B} (c : chain (A * B)) : chain B :=
  {| chain_car n := snd (c n) |}.
Next Obligation. by intros A ? B ? c n i ?; apply (chain_cauchy c n). Qed.
Instance prod_compl `{Compl A, Compl B} : Compl (A * B) := λ c,
  (compl (fst_chain c), compl (snd_chain c)).
Instance prod_cofe `{Cofe A, Cofe B} : Cofe (A * B).
Proof.
  split.
  * intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
    rewrite !equiv_dist; naive_solver.
  * apply _.
  * by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
  * by split.
  * intros c n; split. apply (conv_compl (fst_chain c) n).
    apply (conv_compl (snd_chain c) n).
Qed.
Canonical Structure prodC (A B : cofeT) : cofeT := CofeT (A * B).
Local Instance prod_map_ne `{Dist A, Dist A', Dist B, Dist B'} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodC A B -n> prodC A' B' := CofeMor (prod_map f g).
Instance prodC_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n) (@prodC_map A A' B B').
Proof. intros f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

Instance pair_ne `{Dist A, Dist B} :
  Proper (dist n ==> dist n ==> dist n) (@pair A B) := _.
Instance fst_ne `{Dist A, Dist B} : Proper (dist n ==> dist n) (@fst A B) := _.
Instance snd_ne `{Dist A, Dist B} : Proper (dist n ==> dist n) (@snd A B) := _.
Typeclasses Opaque prod_dist.
