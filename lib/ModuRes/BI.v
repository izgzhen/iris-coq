Require Import Ssreflect.ssreflect Omega.
Require Import PreoMet.
Require Import RA.

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


  (* An ordered type which is antisymmetric and bounded, and has a notion of validity. *)
  Class Bounded `{preoT : preoType T, BIV: validBI, BIT : topBI, BIB : botBI}: Prop :=
    mkBounded {
        pord_antisym:  forall P Q, P ⊑ Q -> Q ⊑ P -> P == Q;
        top_true    :  forall P, P ⊑ top;
        bot_false   :  forall P, bot ⊑ P;
        top_valid   :  forall P, valid P <-> top ⊑ P
      }.

  Class BI `{bT : Bounded} {mT: metric T} {cmT: cmetric T} {pcmT: pcmType T}
        {BIA : andBI} {BIO : orBI} {BII : implBI} {BISC : scBI} {BISI : siBI}: Prop :=
    mkBI {
        and_self    :  forall P, P ⊑ and P P;
        and_projL   :  forall P Q, and P Q ⊑ P;
        and_projR   :  forall P Q, and P Q ⊑ Q;
        and_equiv   :> Proper (equiv ==> equiv ==> equiv) and;
        and_dist n  :> Proper (dist n ==> dist n ==> dist n) and;
        and_pord    :> Proper (pord ++> pord ++> pord) and;
        and_impl    :  forall P Q R, and P Q ⊑ R <-> P ⊑ impl Q R;
        impl_dist n :> Proper (dist n ==> dist n ==> dist n) impl;
        or_injL     :  forall P Q, P ⊑ or P Q;
        or_injR     :  forall P Q, Q ⊑ or P Q;
        or_self     :  forall P, or P P ⊑ P;
        or_equiv    :> Proper (equiv ==> equiv ==> equiv) or;
        or_dist n   :> Proper (dist n ==> dist n ==> dist n) or;
        or_pord     :> Proper (pord ++> pord ++> pord) or;
        sc_comm     :> Commutative sc;
        sc_assoc    :> Associative sc;
        sc_top_unit :  forall P, sc top P == P;
        sc_equiv    :> Proper (equiv ==> equiv ==> equiv) sc;
        sc_dist n   :> Proper (dist n ==> dist n ==> dist n) sc;
        sc_pord     :> Proper (pord ++> pord ++> pord) sc;
        sc_si       :  forall P Q R, sc P Q ⊑ R <-> P ⊑ si Q R;
        si_dist n   :> Proper (dist n ==> dist n ==> dist n) si
      }.
  
  Class ComplBI `{BBI: BI} {BIAll : allBI} {BIXist : xistBI}:Prop :=
    mkCBI {
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
Arguments Bounded T {_ _ _ _ _}.
Arguments BI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments ComplBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments EqBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Delimit Scope bi_scope with bi.
Notation "⊤" := (top) : bi_scope.
Notation "⊥" := (bot) : bi_scope.
Notation "p ∧ q" := (and p q) (at level 39, right associativity) : bi_scope.
Notation "p ∨ q" := (or p q) (at level 51, right associativity) : bi_scope.
Notation "p * q" := (sc p q) (at level 40, left associativity) : bi_scope.
Notation "p → q" := (impl p q) (at level 55, right associativity) : bi_scope.
Notation "P ↔ Q" := ((P → Q) ∧ (Q → P))%bi (at level 95, no associativity) : bi_scope.
Notation "p '-*' q" := (si p q) (at level 55, right associativity) : bi_scope.
Notation "∀ x , p" := (all n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x , p" := (xist n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∀ x : T , p" := (all n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x : T , p" := (xist n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "t1 '===' t2" := (intEq t1 t2) (at level 30) : bi_scope.

Local Open Scope bi.

(* Derive some general BI rules *)
Section BIProps.
  Context {B} `{BI B}.

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

End BIProps.

Section ComplBIProps.
  Context {B} `{ComplBI B}.

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
    move=>HEQ Hφ. transitivity ((t1 === t2) ∧ φ t1).
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

(* Show that any BI can close over "future Us", for U being a CMRA. *)
Section MComplBI.
  Context {B} `{ComplBI B}.
  Context {T} `{CMRA T}.
  Local Obligation Tactic := intros; try resp_set.

  Program Definition mclose : (T -n> B) -n> T -m> B :=
    n[(fun f: T -n> B => m[(fun t => (all (U:=T) (f <M< n[(ra_op t)])))])].
  Next Obligation.
    move=>t1 t2 EQt. eapply all_dist. eapply ndist_umcomp; first reflexivity.
    move=>u. now eapply ra_op_dist.
  Qed.
  Next Obligation.
    intros t1 t2 [t3 EQt]. simpl. eapply all_R=>u.
    simpl. rewrite <-EQt. rewrite-> (comm t3), <-assoc.
    transitivity ((f <M< n[(ra_op t1)]) (t3 · u)%ra); last first.
    - eapply pordR. simpl. reflexivity.
    - eapply all_R. eapply pordR, all_equiv. move=>?. reflexivity.
  Qed.
  Next Obligation.
    intros f1 f2 EQf t. simpl. eapply all_dist. move=>u. simpl. rewrite EQf. reflexivity.
  Qed.

  Lemma mclose_cl f : (mclose f: T -n> B) ⊑ f.
  Proof.
    unfold mclose=>u. simpl.
    transitivity ((f <M< n[(ra_op u)]) 1%ra).
    - eapply all_R. eapply all_pord=>t. reflexivity.
    - simpl. rewrite ra_op_unit2. reflexivity.
  Qed.
  Lemma  mclose_fw (f : T -n> B) u t (HFW : forall u' (HS : u ⊑ u'), t ⊑ f u'):
    t ⊑ mclose f u.
  Proof.
    unfold mclose. simpl. eapply all_R=>u'.
    eapply HFW. exists u'. rewrite comm. reflexivity.
  Qed.

End MComplBI.

(* Monotone functions from a CMRA to a BI form a BI. *)
Section MonotoneExt.
  Context B {eqB: Setoid B} {preoB: preoType B} {BIVB: validBI B} {BIBB: botBI B} {BITB: topBI B} {BB: Bounded B}.
  Context {mB: metric B} {cmB: cmetric B} {pcmB: pcmType B}.
  Context T `{cmraT: CMRA T}.
  Local Open Scope ra.
  Local Open Scope bi.
  
  Local Obligation Tactic := intros; resp_set || mono_resp || eauto with typeclass_instances.

  Global Instance top_mm : topBI (T -m> B) := pcmconst top.
  Global Instance bot_mm : botBI (T -m> B) := pcmconst bot.
  Global Instance valid_mm : validBI (T -m> B) := fun P => forall t, valid (P t).

  Global Instance bounded_mm : Bounded (T -m> B).
  Proof.
    split.
    - intros P Q HPQ HQP t. apply pord_antisym; [apply HPQ | apply HQP].
    - intros P t. apply top_true.
    - intros P t. apply bot_false.
    - intros P. split; intros HV.
      + intros t. simpl morph. unfold const. rewrite <-top_valid. eapply HV.
      + intros t. rewrite ->top_valid. eapply HV.
  Qed.

  Context {BIAB : andBI B} {BIOB: orBI B} {BIIB: implBI B} {BISCB: scBI B} {BISIB: siBI B} {BBI: BI B}.
  Context {BIAllB: allBI B} {BIXistB: xistBI B} {CBBI: ComplBI B}. (* We need this already for upclosing and equality *)
  Context {EQBT: eqBI B} {EQB: EqBI B}.

  Global Program Instance and_mm : andBI (T -m> B) :=
    fun P Q => m[(lift_bin and P Q)].
  Global Program Instance or_mm  : orBI  (T -m> B) :=
    fun P Q => m[(lift_bin or P Q)].

  Global Program Instance impl_mm : implBI (T -m> B) :=
    fun P Q => mclose (lift_bin impl P Q).

  Global Program Instance sc_mm  : scBI (T -m> B) :=
    fun P Q => m[(fun t:T => xist n[(fun ts:T*T => ((Mfst ts · Msnd ts) === t) ∧ (P (Mfst ts) * Q (Msnd ts)))])].
  Next Obligation.
    move=>t1 t2 EQt. rewrite /= -/dist. eapply xist_dist. move=>[ts1 ts2] /=. rewrite -/dist.
    rewrite EQt. reflexivity.
  Qed.
  Next Obligation.
    move=>t1 t2 [tx EQt]. simpl. eapply xist_L. intros [ts1 ts2]. eapply xist_R with (u:=(ts1·tx, ts2)).
    simpl. eapply and_pord; last eapply sc_pord.
    - rewrite !intEq_leibnitz /bi_leibnitz. eapply all_R=>φ/=.
      eapply all_L with (u:= φ <M< ra_op_n tx). simpl. apply pordR.
      eapply impl_equiv; f_equiv.
      + rewrite (comm ts1 tx) (assoc _ ts1). reflexivity.
      + assumption.
    - eapply mu_mono. exists tx. rewrite comm. reflexivity.
    - reflexivity.
  Qed.

  Global Program Instance si_mm : siBI (T -m> B) :=
    fun P Q => m[(fun t1 => all n[(fun t2 => (P t2) -* (Q (t1 · t2)))])].
  Next Obligation.
    move=>u1 u2 EQu. simpl. eapply si_dist.
    - rewrite EQu. reflexivity.
    - rewrite EQu. reflexivity.
  Qed.
  Next Obligation.
    move=>u1 u2 EQu. eapply all_dist. move=>t. simpl. eapply si_dist; first reflexivity.
    rewrite EQu. reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 [t3 EQt]. simpl. eapply all_R=>u.
    simpl. transitivity (P (t3 · u) -* Q (t3 · t1 · u)); last first.
    - rewrite -sc_si. assert (HP: P u ⊑ P (t3 · u)).
      { eapply mu_mono. exists t3. reflexivity. }
      setoid_rewrite HP. rewrite sc_si. eapply si_pord; first reflexivity. eapply mu_mono, pordR.
      rewrite EQt. reflexivity.
    - eapply (all_L (t3 · u)). simpl. eapply si_pord; first reflexivity. eapply mu_mono, pordR.
      rewrite assoc (comm t1). reflexivity.
  Qed.

  (* All of the above preserve all the props it should. *)
  Global Instance and_mm_equiv : Proper (equiv ==> equiv ==> equiv) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance and_mm_dist n : Proper (dist n ==> dist n ==> dist n) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance and_mm_ord : Proper (pord ==> pord ==> pord) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance or_mm_equiv : Proper (equiv ==> equiv ==> equiv) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance or_mm_dist n : Proper (dist n ==> dist n ==> dist n) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance or_mm_ord : Proper (pord ==> pord ==> pord) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance impl_mm_dist n : Proper (dist n ==> dist n ==> dist n) impl_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; apply met_morph_nonexp; intros t; simpl morph.
    apply impl_dist; [apply EQP | apply EQQ].
  Qed.

  Global Instance sc_mm_equiv : Proper (equiv ==> equiv ==> equiv) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_equiv; move=>[t1 t2]. simpl. apply and_equiv; first reflexivity.
    apply sc_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_dist n : Proper (dist n ==> dist n ==> dist n) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_dist; move=>[t1 t2]. simpl morph. apply and_dist; first reflexivity.
    apply sc_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_ord : Proper (pord ++> pord ++> pord) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_pord. intros [t1 t2]. simpl morph. eapply and_pord; first reflexivity.
    apply sc_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance sc_mm_comm : Commutative sc_mm.
  Proof.
    intros f1 f2 t; simpl morph. apply pord_antisym.
    - apply xist_L; move=>[u1 u2]. simpl morph. apply (xist_R (u2, u1)). simpl morph. apply and_pord.
      + apply pordR. apply intEq_equiv; last reflexivity. rewrite comm. reflexivity.
      + rewrite comm. reflexivity.
    - apply xist_L; move=>[u1 u2]. simpl morph. apply (xist_R (u2, u1)). simpl morph. apply and_pord.
      + apply pordR. apply intEq_equiv; last reflexivity. rewrite comm. reflexivity.
      + rewrite comm. reflexivity.
  Qed.

  Program Definition sc_mm_assoc_f1 u1 u2 t (f1 f2 f3: T -n> B) :=
    lift_bin and (umconst ((u1 · u2) === t)) (lift_bin sc (umconst (f1 u1)) n[(fun ts => ((fst ts · snd ts) === u2) ∧ (f2 (fst ts) * f3 (snd ts)))]).

  Program Definition sc_mm_assoc_f2 u1 u2 t (f1 f2 f3: T -n> B) :=
    lift_bin and (umconst ((u1 · u2) === t)) (lift_bin sc n[(fun ts => ((fst ts · snd ts) === u1) ∧ (f1 (fst ts) * f2 (snd ts)))] (umconst (f3 u2))).

  Existing Instance sc_equiv.

  Global Instance sc_mm_assoc : Associative sc_mm.
  Proof.
    intros f1 f2 f3 t; simpl morph. apply pord_antisym.
    - apply xist_L; move=>[u1 u2]. simpl morph.
      transitivity (xist (sc_mm_assoc_f1 u1 u2 t f1 f2 f3)); unfold sc_mm_assoc_f1.
      + etransitivity; last eapply xist_and_r. apply and_pord; first reflexivity.
        etransitivity; last eapply xist_sc_r. apply sc_pord; first reflexivity.
        reflexivity.
      + apply xist_L; move=>[u3 u4]. simpl morph. unfold const.
        apply (xist_R (u1 · u3, u4)). simpl morph. apply and_R; split.
        * transitivity ((u1 · u2) === t ∧ (u3 · u4) === u2).
          { apply and_pord; first reflexivity. setoid_rewrite and_projL.
            apply sc_projR. }
          eapply intEq_rewrite_goal with (φ := intEq_l (u1 · u3 · u4)).
          { rewrite ->and_projL. reflexivity. }
          setoid_rewrite and_projR. eapply intEq_rewrite_goal with (t2:=u2) (φ := intEq_l (u1 · u3 · u4) <M< ra_op_n u1).
          { reflexivity. }
          simpl morph. eapply intEqR. now rewrite assoc.
        * transitivity ((f1 u1 * f2 u3) * f3 u4).
          { rewrite ->and_projR, and_projR. rewrite assoc. reflexivity. }
          apply sc_pord; last reflexivity.
          apply (xist_R (u1, u3)). simpl morph.
          apply and_R; split; last reflexivity.
          setoid_rewrite <-intEq_refl. apply top_true.
    - apply xist_L; move=>[u1 u2]. simpl morph.
      transitivity (xist (sc_mm_assoc_f2 u1 u2 t f1 f2 f3)); unfold sc_mm_assoc_f2.
      + etransitivity; last eapply xist_and_r. apply and_pord; first reflexivity.
        eapply xist_sc.
      + apply xist_L; move=>[u3 u4]. simpl morph. unfold const.
        apply (xist_R (u3, u4·u2)). simpl morph. apply and_R; split.
        * transitivity ((u1 · u2) === t ∧ (u3 · u4) === u1).
          { apply and_pord; first reflexivity. rewrite ->and_projL, sc_projL. reflexivity. }
          eapply intEq_rewrite_goal with (φ := intEq_l (u3 · (u4 · u2))).
          { rewrite ->and_projL. reflexivity. }
          rewrite ->and_projR. simpl morph. eapply intEq_rewrite_goal with (t2:=u1) (φ := intEq_l (u3 · (u4 · u2)) <M< Mswap ra_op_n u2).
          { reflexivity. }
          simpl morph. eapply intEqR. now rewrite assoc.
        * transitivity (f1 u3 * (f2 u4 * f3 u2)).
          { rewrite ->and_projR, and_projR. rewrite assoc. reflexivity. }
          apply sc_pord; first reflexivity.
          apply (xist_R (u4, u2)). simpl morph. apply and_R; split; last reflexivity.
          setoid_rewrite <-intEq_refl. apply top_true.
  Qed.

  Global Instance si_mm_dist n : Proper (dist n ==> dist n ==> dist n) si_mm.
  Proof.    
    intros P1 P2 EQP Q1 Q2 EQQ t. simpl morph.
    apply all_dist; move=>u. simpl morph.
    apply si_dist; [apply EQP | apply EQQ].
  Qed.

  Global Program Instance bi_mm : BI (T -m> B).
  Next Obligation.
    intros t; simpl morph; apply and_self.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply and_projL.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply and_projR.
  Qed.
  Next Obligation.
    split; intros HH t; simpl morph.
    - apply mclose_fw; intros t' Subt; specialize (HH t'); simpl morph in *.
      rewrite ->Subt, <- and_impl; assumption.
    - rewrite ->and_impl, (HH t); apply mclose_cl.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_injL.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_injR.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_self.
  Qed.
  Next Obligation.
    intros t; simpl morph. apply pord_antisym.
    - apply xist_L;move=>[ts1 ts2]. simpl morph.
      eapply intEq_rewrite_goal with (φ := P).
      { rewrite ->and_projL. reflexivity. }
      rewrite ->and_projR, ->sc_projR. apply mu_mono. exists ts1. reflexivity.
    - apply (xist_R (1, t)). simpl morph. apply and_R; split.
      + eapply intEqR. now rewrite ra_op_unit.
      + unfold const. rewrite sc_top_unit. reflexivity.
  Qed.
  Next Obligation.
    split; move=>HLE t.
    - simpl. apply all_R=>u. simpl morph.
      eapply sc_si. rewrite <-(HLE _). simpl morph. apply (xist_R (t, u)). simpl morph.
      apply and_R; split; last reflexivity.
      eapply intEqR. reflexivity.
    - simpl. apply xist_L;move=>[u1 u2]. simpl morph.
      eapply intEq_rewrite_goal with (φ := R).
      { rewrite ->and_projL. reflexivity. }
      rewrite ->and_projR=>{t}. apply sc_si. rewrite ->HLE=>{HLE}. simpl.
      apply (all_L u2). reflexivity.
  Qed.

  Global Program Instance all_mm : allBI (T -m> B) :=
    fun U eqU mU cmU R =>
      m[(fun t => all n[(fun u => R u t)])].
  Next Obligation.
    intros t1 t2 EQt; apply all_dist; intros u; simpl morph.
    rewrite EQt; reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 Subt; apply all_pord; intros u; simpl morph.
    rewrite ->Subt; reflexivity.
  Qed.

  Global Program Instance xist_mm : xistBI (T -m> B) :=
    fun U eqU mU cmU R =>
      m[(fun t => xist n[(fun u => R u t)])].
  Next Obligation.
    intros t1 t2 EQt; apply xist_dist; intros u; simpl morph.
    rewrite EQt; reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 Subt; apply xist_pord; intros u; simpl morph.
    rewrite ->Subt; reflexivity.
  Qed.

  Section Quantifiers.
    Context V `{cmV : cmetric V}.

    Global Instance all_mm_dist n : Proper (dist (T := V -n> T -m> B) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply all_dist; intros u; simpl morph; apply EQR.
    Qed.

    Global Instance xist_mm_dist n : Proper (dist (T := V -n> T -m> B)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply xist_dist; intros u; simpl morph; apply EQR.
    Qed.

  End Quantifiers.

  Global Program Instance cbi_mm : ComplBI (T -m> B).
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- all_R; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *; rewrite <- all_R in HH.
      simpl morph in HH; apply HH.
  Qed.
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- xist_L; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *.
      rewrite <- xist_L in HH; simpl morph in HH; apply HH.
  Qed.

End MonotoneExt.

Section MonotoneEQ.
  Context B `{LB: EqBI B}
          T `{cmraT : CMRA T}.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Global Instance eq_mm : eqBI (T -m> B) :=
    fun U {eqU mU cmU u1 u2} => pcmconst (u1 === u2).

  Global Instance eqbi_mm : EqBI (T -m> B).
  Proof.
    split; intros.
    - move=>t1 t2 EQt u1 u2 EQu x. simpl morph. unfold const. apply intEq_equiv; assumption.
    - move=>t1 t2 EQt u1 u2 EQu x. simpl morph. unfold const. apply intEq_dist; assumption.
    - move=>x. simpl morph. unfold const. rewrite intEq_leibnitz /bi_leibnitz. apply pord_antisym.
      + apply all_R=>f. simpl morph. apply all_R=>t. simpl morph.
        pose (φ := fun u => f u (x·t)%ra).
        assert (φ_dist: forall n, Proper (dist n ==> dist n) φ).
        { clear. move=>n u1 u2 EQu. unfold φ. rewrite EQu. reflexivity. } 
        apply (all_L n[(φ)]). simpl morph. unfold φ. reflexivity.
      + apply all_R=>f. simpl morph.
        pose (φ := fun u => (pcmconst (T:=T) (U:=B) (f u))).
        assert (φ_dist: forall n, Proper (dist n ==> dist n) φ).
        { clear. move=>n u1 u2 EQu r. unfold φ, pcmconst. simpl morph. unfold const. rewrite EQu. reflexivity. }
        apply (all_L n[(φ)]). simpl morph. apply (all_L x)%ra. simpl morph. unfold const. apply impl_pord.
        * reflexivity.
        * reflexivity.
    - move=>t. simpl morph. unfold const. apply (xist_R (1%ra, t)). simpl morph.
      apply and_R; split; last now eapply intEq_sc.
      apply intEqR. now rewrite ra_op_unit.
  Qed.

End MonotoneEQ.
