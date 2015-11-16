Require Export iris.cofe prelude.fin_maps.
Require Import prelude.pmap prelude.nmap prelude.zmap.
Require Import prelude.stringmap prelude.natmap.
Local Obligation Tactic := idtac.

(** option *)
Inductive option_dist `{Dist A} : Dist (option A) :=
  | option_0_dist (x y : option A) : x ={0}= y
  | Some_dist n x y : x ={n}= y → Some x ={n}= Some y
  | None_dist n : None ={n}= None.
Existing Instance option_dist.
Program Definition option_chain `{Cofe A}
    (c : chain (option A)) (x : A) (H : c 1 = Some x) : chain A :=
  {| chain_car n := from_option x (c n) |}.
Next Obligation.
  intros A ???? c x ? n i ?; simpl; destruct (decide (i = 0)) as [->|].
  { by replace n with 0 by lia. }
  feed inversion (chain_cauchy c 1 i); auto with lia congruence.
  feed inversion (chain_cauchy c n i); simpl; auto with lia congruence.
Qed.
Instance option_compl `{Cofe A} : Compl (option A) := λ c,
  match Some_dec (c 1) with
  | inleft (exist x H) => Some (compl (option_chain c x H)) | inright _ => None
  end.
Instance option_cofe `{Cofe A} : Cofe (option A).
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
Instance Some_ne `{Dist A} : Proper (dist n ==> dist n) Some.
Proof. by constructor. Qed.
Instance option_fmap_ne `{Dist A, Dist B} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n==>dist n) (fmap (M:=option) f).
Proof. by intros Hf; destruct 1; constructor; apply Hf. Qed.

(** Finite maps *)
Section map.
  Context `{FinMap K M}.
  Global Instance map_dist `{Dist A} : Dist (M A) := λ n m1 m2,
    ∀ i, m1 !! i ={n}= m2 !! i.
  Program Definition map_chain `{Dist A} (c : chain (M A))
    (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
  Next Obligation. by intros A ? c k n i ?; apply (chain_cauchy c). Qed.
  Global Instance map_compl `{Cofe A} : Compl (M A) := λ c,
    map_imap (λ i _, compl (map_chain c i)) (c 1).
  Global Instance map_cofe `{Cofe A} : Cofe (M A).
  Proof.
    split.
    * intros m1 m2; split.
      + by intros Hm n k; apply equiv_dist.
      + intros Hm k; apply equiv_dist; intros n; apply Hm.
    * intros n; split.
      + by intros m k.
      + by intros m1 m2 ? k.
      + by intros m1 m2 m3 ?? k; transitivity (m2 !! k).
    * by intros n m1 m2 ? k; apply dist_S.
    * by intros m1 m2 k.
    * intros c n k; unfold compl, map_compl; rewrite lookup_imap.
      destruct (decide (n = 0)) as [->|]; [constructor|].
      feed inversion (λ H, chain_cauchy c 1 n H k); simpl; auto with lia.
      by rewrite conv_compl; simpl; apply reflexive_eq.
  Qed.
  Global Instance lookup_ne `{Dist A} n k :
    Proper (dist n ==> dist n) (lookup k : M A → option A).
  Proof. by intros m1 m2. Qed.
  Instance map_fmap_ne `{Dist A, Dist B} (f : A → B) n :
    Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (fmap (M:=M) f).
  Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
  Definition mapC (A : cofeT) : cofeT := CofeT (M A).
  Definition mapC_map {A B} (f: A -n> B) : mapC A -n> mapC B :=
    CofeMor (fmap f : mapC A → mapC B).
  Global Instance mapC_map_ne {A B} n :
    Proper (dist n ==> dist n) (@mapC_map A B).
  Proof.
    intros f g Hf m k; simpl; rewrite !lookup_fmap.
    destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
  Qed.
End map.
Arguments mapC {_} _ {_ _ _ _ _ _ _ _ _} _.

Canonical Structure natmapC := mapC natmap.
Definition natmapC_map {A B}
  (f : A -n> B) : natmapC A -n> natmapC B := mapC_map f.
Canonical Structure PmapC := mapC Pmap.
Definition PmapC_map {A B} (f : A -n> B) : PmapC A -n> PmapC B := mapC_map f.
Canonical Structure NmapC := mapC Nmap.
Definition NmapC_map {A B} (f : A -n> B) : NmapC A -n> NmapC B := mapC_map f.
Canonical Structure ZmapC := mapC Zmap.
Definition ZmapC_map {A B} (f : A -n> B) : ZmapC A -n> ZmapC B := mapC_map f.
Canonical Structure stringmapC := mapC stringmap.
Definition stringmapC_map {A B}
  (f : A -n> B) : stringmapC A -n> stringmapC B := mapC_map f.
