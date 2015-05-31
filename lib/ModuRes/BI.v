Require Import Ssreflect.ssreflect Omega.
Require Import PreoMet.

Set Bullet Behavior "Strict Subproofs".

Section CompleteBI.
  Context {T : Type}.
  Local Open Scope type.

  Class validBI:= valid: T -> Prop.
  Class topBI  := top  : T.
  Class botBI  := bot  : T.
  Class andBI  := and  : T -> T -> T.
  Class orBI   := or   : T -> T -> T.
  Class implBI := impl : T -> T -> T.
  Class scBI   := sc   : T -> T -> T.
  Class siBI   := si   : T -> T -> T.
  Class eqBI   := intEq : forall {U} `{pU : cmetric U}, U -> U -> T.
  (* This does not go to full generality: Compared to "adjoint of the projection", we fix
     the type that's "kept" to be unit (and simplify accordingly). *)
  Class allBI  `{cmT : cmetric T} :=
    all  : forall {U} `{pU : cmetric U}, (U -n> T) -> T.
  Class xistBI `{cmT : cmetric T} :=
    xist : forall {U} `{pU : cmetric U}, (U -n> T) -> T.


  (* Lattices. *)
  Class Lattice `{preoT : pcmType T, BIV: validBI, BIT : topBI, BIB : botBI, BIA : andBI, BIO : orBI}: Prop :=
    mkBounded {
        (* Anti-symmetry: Necessary for commutativity of addition, and commutativity of SC of the lifted BI *)
        pord_antisym:  forall P Q, P ⊑ Q -> Q ⊑ P -> P == Q;
        top_true    :  forall P, P ⊑ top;
        bot_false   :  forall P, bot ⊑ P;
        top_valid   :  forall P, valid P <-> top ⊑ P;
        consistency :  ~valid bot;
        and_self    :  forall P, P ⊑ and P P;
        and_projL   :  forall P Q, and P Q ⊑ P;
        and_projR   :  forall P Q, and P Q ⊑ Q;
        and_equiv   :> Proper (equiv ==> equiv ==> equiv) and;
        and_dist n  :> Proper (dist n ==> dist n ==> dist n) and;
        and_pord    :> Proper (pord ++> pord ++> pord) and;
        or_injL     :  forall P Q, P ⊑ or P Q;
        or_injR     :  forall P Q, Q ⊑ or P Q;
        or_self     :  forall P, or P P ⊑ P;
        or_equiv    :> Proper (equiv ==> equiv ==> equiv) or;
        or_dist n   :> Proper (dist n ==> dist n ==> dist n) or;
        or_pord     :> Proper (pord ++> pord ++> pord) or
      }.

  Class ComplBI `{bL : Lattice}  {BII : implBI} {BISC : scBI} {BISI : siBI} {BIAll : allBI} {BIXist : xistBI}: Prop :=
    mkCBI {
        and_impl    :  forall P Q R, and P Q ⊑ R <-> P ⊑ impl Q R;
        impl_dist n :> Proper (dist n ==> dist n ==> dist n) impl;
        sc_comm     :> Commutative sc;
        sc_assoc    :> Associative sc;
        sc_top_unit :  forall P, sc top P == P;
        sc_equiv    :> Proper (equiv ==> equiv ==> equiv) sc;
        sc_dist n   :> Proper (dist n ==> dist n ==> dist n) sc;
        sc_pord     :> Proper (pord ++> pord ++> pord) sc;
        sc_si       :  forall P Q R, sc P Q ⊑ R <-> P ⊑ si Q R;
        si_dist n   :> Proper (dist n ==> dist n ==> dist n) si;
        all_R      U `{cmU : cmetric U} :
          forall P (Q : U -n> T), (forall u, P ⊑ Q u) <-> P ⊑ all Q;
        all_dist   U `{cmU : cmetric U} n :> Proper (dist n ==> dist n) all;
        xist_L     U `{cmU : cmetric U} :
          forall (P : U -n> T) Q, (forall u, P u ⊑ Q) <-> xist P ⊑ Q;
        xist_dist  U `{cmU : cmetric U} n :> Proper (dist n ==> dist n) xist
     }.

  (* A BI that can reflect equality. We don't bother with "a specific type here", as we already did
     not bother with that for completion. *)
  Program Definition bi_leibnitz `{BCBI: ComplBI} {U: Type} `{cmetric U} (u1 u2: U): T :=
    all n[(fun p: U -n> T => impl (p u1) (p u2))].
  Next Obligation.
    move=>p1 p2 EQp. simpl. eapply impl_dist; rewrite EQp; reflexivity.
  Qed.
  
  Class EqBI `{BCBI: ComplBI} {BIEQ: eqBI}: Prop :=
    { intEq_equiv  U `{cmU : cmetric U}   :> Proper (equiv ==> equiv ==> equiv) intEq;
      intEq_dist   U `{cmU : cmetric U} n :> Proper (dist n ==> dist n ==> dist n) intEq;
      intEq_leibnitz {U} `{cmU : cmetric U} (u1 u2: U) : intEq u1 u2 == bi_leibnitz u1 u2;
      intEq_sc       {U} `{cmU : cmetric U} (u1 u2: U) P : and (intEq u1 u2) P ⊑ sc (intEq u1 u2) P
    }.

End CompleteBI.

Arguments validBI  : default implicits.
Arguments topBI  : default implicits.
Arguments botBI  : default implicits.
Arguments andBI  : default implicits.
Arguments orBI   : default implicits.
Arguments implBI : default implicits.
Arguments scBI   : default implicits.
Arguments siBI   : default implicits.
Arguments eqBI   : default implicits.
Arguments allBI  T {_ _ _}.
Arguments xistBI T {_ _ _}.
Arguments Lattice T {_ _ _ _ _ _ _ _ _ _}.
Arguments ComplBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments EqBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Delimit Scope bi_scope with bi.
Notation "⊤" := (top) : bi_scope.
Notation "⊥" := (bot) : bi_scope.
Notation "p ∧ q" := (and p q) (at level 39, right associativity) : bi_scope.
Notation "p ∨ q" := (or p q) (at level 51, right associativity) : bi_scope.
Notation "p * q" := (sc p q) (at level 40, left associativity) : bi_scope.
Notation "p → q" := (impl p q) (at level 55, right associativity) : bi_scope.
Notation "P ↔ Q" := ((P → Q) ∧ (Q → P))%bi (at level 57, no associativity) : bi_scope.
Notation "p '-*' q" := (si p q) (at level 55, right associativity) : bi_scope.
Notation "∀ x , p" := (all n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x , p" := (xist n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∀ x : T , p" := (all n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x : T , p" := (xist n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "t1 '===' t2" := (intEq t1 t2) (at level 35) : bi_scope.

Local Open Scope bi_scope.

(* Derive some general BI rules *)
Section LatticeProps.
  Context {B} `{Lattice B}.

  Lemma and_R P Q R: (R ⊑ P /\ R ⊑ Q) <-> R ⊑ P ∧ Q.
  Proof.
    split.
    - move=>[H1 H2]. transitivity (R ∧ R).
      + apply and_self.
      + apply and_pord; assumption.
    - move=>EQ. split; (transitivity (P ∧ Q); first assumption).
      + apply and_projL.
      + apply and_projR.
  Qed.

  Lemma and_pcomm P Q: and P Q ⊑ and Q P.
  Proof.
    apply and_R; split.
    - apply and_projR.
    - apply and_projL.
  Qed.

  Global Instance and_comm: Commutative and.
  Proof.
    move=>b1 b2. apply pord_antisym; now apply and_pcomm.
  Qed.

  Global Instance and_assoc: Associative and.
  Proof.
    move=>b1 b2 b3. apply pord_antisym.
    - apply and_R; split; first (apply and_R; split).
      + apply and_projL.
      + rewrite ->and_projR. apply and_projL.
      + rewrite ->and_projR. apply and_projR.
    - apply and_R; split; last (apply and_R; split).
      + rewrite ->and_projL. apply and_projL.
      + rewrite ->and_projL. apply and_projR.
      + apply and_projR.
  Qed.

  Lemma or_L P Q R: (P ⊑ R /\ Q ⊑ R) <-> or P Q ⊑ R.
  Proof.
    split.
    - move=>[HPR HQR]. transitivity (R ∨ R).
      + apply or_pord; [apply HPR|apply HQR].
      + apply or_self.
    - move=>HPQR. rewrite <-HPQR=>{HPQR R}. split.
      + apply or_injL.
      + apply or_injR.
  Qed.
  
  Lemma or_pcomm P Q: or P Q ⊑ or Q P.
  Proof.
    apply or_L. split; [apply or_injR|apply or_injL].
  Qed.

  Global Instance or_comm: Commutative or.
  Proof.
    move=>b1 b2. apply pord_antisym; now apply or_pcomm.
  Qed.

  Global Instance or_assoc: Associative or.
  Proof.
    move=>b1 b2 b3. apply pord_antisym.
    - apply or_L; split; last (apply or_L; split).
      + rewrite <-or_injL. apply or_injL.
      + rewrite <-or_injL. apply or_injR.
      + apply or_injR.
    - apply or_L; split; first (apply or_L; split).
      + apply or_injL.
      + rewrite <-or_injR. apply or_injL.
      + rewrite <-or_injR. apply or_injR.
  Qed.
End LatticeProps.

Section ComplBIProps.
  Context {B} `{ComplBI B}.
  
  Global Instance impl_pord :
    Proper (pord --> pord ++> pord) impl.
  Proof.
    move=>P1 P2 EQP Q1 Q2 EQQ. rewrite <-and_impl. rewrite <-EQQ=>{Q2 EQQ}.
    unfold flip in EQP. rewrite ->EQP, ->and_impl. reflexivity.
  Qed.

  Global Instance impl_equiv :
    Proper (equiv ==> equiv ==> equiv) impl.
  Proof.
    move=>P1 P2 EQP Q1 Q2 EQQ. apply pord_antisym; apply impl_pord; rewrite ?EQP ?EQQ; reflexivity.
  Qed.

  Lemma modus_ponens P Q R: P ⊑ Q -> P ⊑ Q → R -> P ⊑ R.
  Proof.
    move=>HQ HQR. transitivity ((Q → R) ∧ Q).
    - apply and_R; split; assumption.
    - clear P HQ HQR. apply and_impl. reflexivity.
  Qed.
  
  Global Instance si_pord :
    Proper (pord --> pord ++> pord) si.
  Proof.
    move=>P1 P2 EQP Q1 Q2 EQQ. rewrite <-sc_si. rewrite <-EQQ=>{Q2 EQQ}.
    unfold flip in EQP. rewrite ->EQP. rewrite ->sc_si. reflexivity.
  Qed.

  Global Instance si_equiv :
    Proper (equiv ==> equiv ==> equiv) si.
  Proof.
    move=>P1 P2 EQP Q1 Q2 EQQ. apply pord_antisym; apply si_pord; rewrite ?EQP ?EQQ; reflexivity.
  Qed.
  
  Lemma sc_projR P Q: P * Q ⊑ Q.
  Proof.
    transitivity (top * Q).
    - apply sc_pord; last reflexivity. apply top_true.
    - apply pordR. apply sc_top_unit.
  Qed.

  Lemma sc_projL P Q: P * Q ⊑ P.
  Proof.
    rewrite comm. apply sc_projR.
  Qed.

  Lemma sc_and P Q: P * Q ⊑ P ∧ Q.
  Proof.
    apply and_R; split.
    - apply sc_projL.
    - apply sc_projR.
  Qed.

  Lemma sc_or P Q R: (P ∨ Q) * R ⊑ (P * R) ∨ (Q * R).
  Proof.
    apply sc_si. apply or_L. split; apply sc_si.
    - apply or_injL.
    - apply or_injR.
  Qed.

  Lemma all_L {U} `{cmU : cmetric U} u (P: U -n> B) Q:
    P u ⊑ Q -> all P ⊑ Q.
  Proof.
    move=>Hpq. rewrite <-Hpq=>{Hpq Q}.
    specialize (all_R _ (all P) P)=>Hall. eapply Hall. reflexivity.
  Qed.

  Global Instance all_pord U `{cmU : cmetric U} :
    Proper (pord ++> pord) all.
  Proof.
    move=>f1 f2 Hf. apply all_R=>u. rewrite <-Hf.
    apply (all_L u). reflexivity.
  Qed.

  Global Instance all_equiv U `{cmU : cmetric U} :
    Proper (equiv ==> equiv) all.
  Proof.
    move=>f1 f2 Hf. apply pord_antisym; eapply all_pord; rewrite Hf; reflexivity.
  Qed.

  Lemma all_and U `{cmU : cmetric U} : (* the converse does not hold for empty U *)
    forall (P : U -n> B) Q, (all P) ∧ Q ⊑ all (lift_bin and P (umconst Q)).
  Proof.
    move=>P Q.
    apply all_R=>u. apply and_impl. apply (all_L u). apply and_impl. reflexivity.
  Qed.

  Lemma all_sc U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, (all P) * Q ⊑ all (lift_bin sc P (umconst Q)).
  Proof.
    move=>P Q. apply all_R=>u. apply sc_si.
    apply (all_L u). apply sc_si. reflexivity.
  Qed.

  Lemma all_sc_r U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, Q * (all P) ⊑ all (lift_bin sc (umconst Q) P).
  Proof.
    move=>P Q. rewrite (comm Q). etransitivity; first eapply all_sc.
    eapply all_pord. move=>u. simpl morph. rewrite comm. reflexivity.
  Qed.

  Lemma all_and_r U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, Q ∧ (all P) ⊑ all (lift_bin and (umconst Q) P).
  Proof.
    move=>P Q. rewrite (comm Q). etransitivity; first eapply all_and.
    eapply all_pord. move=>u. simpl morph. rewrite comm. reflexivity.
  Qed.


  Lemma xist_R {U} `{cmU : cmetric U} u P (Q: U -n> B):
    P ⊑ Q u -> P ⊑ xist Q.
  Proof.
    move=>Hpq. rewrite ->Hpq=>{Hpq P}.
    specialize (xist_L _ Q (xist Q))=>Hxist.
    eapply Hxist. reflexivity.
  Qed. 

  Global Instance xist_pord U `{cmU : cmetric U} :
    Proper (pord ++> pord) xist.
  Proof.
    move=>f1 f2 Hf. apply xist_L=>u. rewrite ->Hf.
    apply (xist_R u). reflexivity.
  Qed.

  Global Instance xist_equiv U `{cmU : cmetric U} :
    Proper (equiv ==> equiv) xist.
  Proof.
    move=>f1 f2 Hf. apply pord_antisym; eapply xist_pord; rewrite Hf; reflexivity.
  Qed.

  Lemma xist_and U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, (xist P) ∧ Q ⊑ xist (lift_bin and P (umconst Q)).
  Proof.
    move=>P Q. apply and_impl.
    apply xist_L=>u. apply and_impl.
    apply (xist_R u). simpl morph. reflexivity.
  Qed.

  Lemma xist_sc U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, (xist P) * Q ⊑ xist (lift_bin sc P (umconst Q)).
  Proof.
    move=>P Q. apply sc_si.
    apply xist_L=>u. apply sc_si.
    apply (xist_R u). simpl morph. reflexivity.
  Qed.

  Lemma xist_sc_r U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, Q * (xist P) ⊑ xist (lift_bin sc (umconst Q) P).
  Proof.
    move=>P Q. rewrite (comm Q). etransitivity; first eapply xist_sc.
    eapply xist_pord. move=>u. simpl morph. rewrite comm. reflexivity.
  Qed.

  Lemma xist_and_r U `{cmU : cmetric U} :
    forall (P : U -n> B) Q, Q ∧ (xist P) ⊑ xist (lift_bin and (umconst Q) P).
  Proof.
    move=>P Q. rewrite (comm Q). etransitivity; first eapply xist_and.
    eapply xist_pord. move=>u. simpl morph. rewrite comm. reflexivity.
  Qed.
End ComplBIProps.

Section EqBIProps.
  Context {B} `{EqBI B}.

  Program Definition intEq_l {T} `{cmT : cmetric T} t1: T -n> B :=
    n[(fun t2 => t1 === t2)].  Next Obligation.  move=>u1 u2
    EQu. simpl. rewrite EQu. reflexivity.  Qed.

  Program Definition intEq_r {T} `{cmT : cmetric T} t2: T -n> B :=
    n[(fun t1 => t1 === t2)].
  Next Obligation.
    move=>u1 u2 EQu. simpl. rewrite EQu. reflexivity.
  Qed.

  Lemma intEq_refl {T} `{_ : cmetric T} t:
    (⊤:B) ⊑ (t === t).
  Proof.
    rewrite intEq_leibnitz /bi_leibnitz. apply all_R=>P. simpl morph.
    apply and_impl. apply and_projR.
  Qed.

  Lemma intEq_rewrite_goal {T} `{cmetric T} (t1 t2: T) P (φ: _ -n> B):
    P ⊑ t1 === t2 -> P ⊑ φ t1 -> P ⊑ φ t2.
  Proof.
    move=>HEQ Hφ. transitivity (t1 === t2 ∧ φ t1).
    - apply and_R. split; assumption.
    - move=>{P HEQ Hφ}. rewrite -/pord. apply and_impl. rewrite intEq_leibnitz /bi_leibnitz.
      apply (all_L φ). simpl morph. reflexivity. 
  Qed.

  Lemma intEq_sym {T} `{cmetric T} (t1 t2: T):
    t1 === t2 ⊑ t2 === t1.
  Proof.
    rewrite intEq_leibnitz /bi_leibnitz.
    apply (all_L (intEq_r t1)). simpl morph. rewrite <-intEq_refl.
    eapply modus_ponens; last reflexivity.
    apply top_true.
  Qed.

  Lemma intEqR {T} `{cmetric T} (t1 t2: T) P:
    t1 == t2 -> P ⊑ t1 === t2.
  Proof.
    move=>EQ. transitivity (t1 === t1).
    - setoid_rewrite <-intEq_refl. apply top_true.
    - apply pordR. now apply intEq_equiv.
  Qed.

End EqBIProps.

