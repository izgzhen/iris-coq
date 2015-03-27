Require Import PreoMet.
Require Import RA SPred.

Section CompleteBI.
  Context {T : Type}.

  Class topBI  := top  : T.
  Class botBI  := bot  : T.
  Class andBI  := and  : T -> T -> T.
  Class orBI   := or   : T -> T -> T.
  Class implBI := impl : T -> T -> T.
  Class scBI   := sc   : T -> T -> T.
  Class siBI   := si   : T -> T -> T.
  Class allBI  `{cmT : cmetric T} :=
    all  : forall {U} `{pU : cmetric U}, (U -n> T) -> T.
  Class xistBI `{cmT : cmetric T} :=
    xist : forall {U} `{pU : cmetric U}, (U -n> T) -> T.

  Section Lift.
    Context (f : T -> T -> T) `{cmT : cmetric T}
            {fequiv : Proper (equiv ==> equiv ==> equiv) f}
            {fdist : forall n, Proper (dist n ==> dist n ==> dist n) f}
            {U} `{cmU : cmetric U} (P : U -n> T) (Q : U -n> T).

    Local Obligation Tactic := intros; resp_set.

    Program Definition lift_bin : U -n> T :=
      n[(fun u => f (P u) (Q u))].

  End Lift.

  Class Bounded `{pcmT : pcmType T, BIT : topBI, BIB : botBI}: Prop :=
    mkBounded {
        top_true    :  forall P, P ⊑ top;
        bot_false   :  forall P, bot ⊑ P
      }.

  Class ComplBI `{pcmT : Bounded, BIA : andBI, BIO : orBI, BII : implBI, BISC : scBI, BISI : siBI}
        {BIAll : allBI} {BIXist : xistBI} : Prop :=
    mkCBI {
        and_self    :  forall P, P ⊑ and P P;
        and_projL   :  forall P Q, and P Q ⊑ P;
        and_projR   :  forall P Q, and P Q ⊑ Q;
        and_equiv   :> Proper (equiv ==> equiv ==> equiv) and;
        and_dist n  :> Proper (dist n ==> dist n ==> dist n) and;
        and_pord    :> Proper (pord ++> pord ++> pord) and;
        and_impl    :  forall P Q R, and P Q ⊑ R <-> P ⊑ impl Q R;
        impl_equiv  :> Proper (equiv ==> equiv ==> equiv) impl;
        impl_dist n :> Proper (dist n ==> dist n ==> dist n) impl;
        impl_pord   :> Proper (pord --> pord ++> pord) impl;
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
        si_equiv    :> Proper (equiv ==> equiv ==> equiv) si;
        si_dist n   :> Proper (dist n ==> dist n ==> dist n) si;
        si_pord     :> Proper (pord --> pord ++> pord) si;
        all_R      U `{cmU : cmetric U} :
          forall P (Q : U -n> T), (forall u, P ⊑ Q u) <-> P ⊑ all Q;
        all_equiv  U `{cmU : cmetric U} :> Proper (equiv ==> equiv) all;
        all_dist   U `{cmU : cmetric U} n :> Proper (dist n ==> dist n) all;
        all_pord   U `{cmU : cmetric U} (P Q : U -n> T) :
          (forall u, P u ⊑ Q u) -> all P ⊑ all Q;
        xist_L     U `{cmU : cmetric U} :
          forall (P : U -n> T) Q, (forall u, P u ⊑ Q) <-> xist P ⊑ Q;
        xist_sc    U `{cmU : cmetric U} : (* RJ: Where does this come from? Why is there nothing similar for all? *)
          forall (P : U -n> T) Q, sc (xist P) Q ⊑ xist (lift_bin sc P (umconst Q));
        xist_equiv U `{cmU : cmetric U} :> Proper (equiv ==> equiv) xist;
        xist_dist  U `{cmU : cmetric U} n :> Proper (dist n ==> dist n) xist;
        xist_pord  U `{cmU : cmetric U} (P Q : U -n> T) :
          (forall u, P u ⊑ Q u) -> xist P ⊑ xist Q
      }.

End CompleteBI.

Arguments topBI  : default implicits.
Arguments botBI  : default implicits.
Arguments andBI  : default implicits.
Arguments orBI   : default implicits.
Arguments implBI : default implicits.
Arguments scBI   : default implicits.
Arguments siBI   : default implicits.
Arguments allBI  T {_ _ _}.
Arguments xistBI T {_ _ _}.
Arguments Bounded T {_ _ _ _ _ _ _}.
Arguments ComplBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Class Later (T : Type) `{Bounded T} :=
  { later : T -m> T;
    later_mon (t : T) : t ⊑ later t;
    later_contr : contractive later;
    loeb (t : T) (HL : later t ⊑ t) : top ⊑ t
  }.

Arguments Build_Later T {_ _ _ _ _ _ _ _} _ _ _ _.

Delimit Scope bi_scope with bi.
Notation " ▹ p " := (later p) (at level 20) : bi_scope.
Notation "⊤" := (top) : bi_scope.
Notation "⊥" := (bot) : bi_scope.
Notation "p ∧ q" := (and p q) (at level 39, right associativity) : bi_scope.
Notation "p ∨ q" := (or p q) (at level 51, right associativity) : bi_scope.
Notation "p * q" := (sc p q) (at level 40, left associativity) : bi_scope.
Notation "p → q" := (impl p q) (at level 55, right associativity) : bi_scope.
Notation "p '-*' q" := (si p q) (at level 55, right associativity) : bi_scope.
Notation "∀ x , p" := (all n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x , p" := (xist n[(fun x => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∀ x : T , p" := (all n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.
Notation "∃ x : T , p" := (xist n[(fun x : T => p)]) (at level 60, x ident, right associativity) : bi_scope.

Section SPredBI.
  Local Obligation Tactic := intros; eauto with typeclass_instances.

  (* Standard interpretations of propositional connectives. *)
  Global Program Instance top_sp : topBI SPred := sp_top.
  Global Program Instance bot_sp : botBI SPred := sp_c False.

  Global Instance bounded_sp : Bounded SPred.
  Proof.
    split; intro.
    - intros n _; exact I.
    - intros n HC; contradiction HC.
  Qed.

  Global Program Instance and_sp : andBI SPred :=
    fun P Q =>
      mkSPred (fun n => P n /\ Q n) _.
  Next Obligation.
    intros n m HLe; rewrite HLe; tauto.
  Qed.
  Global Program Instance or_sp : orBI SPred :=
    fun P Q =>
      mkSPred (fun n => P n \/ Q n) _.
  Next Obligation.
    intros n m HLe; rewrite HLe; tauto.
  Qed.

  Global Program Instance impl_sp : implBI SPred :=
    fun P Q =>
      mkSPred (fun n => forall m, m <= n -> P m -> Q m) _.
  Next Obligation.
    intros n m HLe HImp k HLe' HP.
    apply HImp; try (etransitivity; eassumption); assumption.
  Qed.
  
  (* BI connectives: Boring. We'd actually want just a Heyting Algebra for SPred, but whatever. *)
  Global Instance sc_sp : scBI SPred := and_sp.
  Global Instance si_sp : siBI SPred := impl_sp.

  (* Quantifiers. *)
  Global Program Instance all_sp : allBI SPred :=
    fun T eqT mT cmT R =>
      mkSPred (fun n => forall t, R t n) _.
  Next Obligation.
    intros n m HLe HR t. rewrite HLe; apply HR.
  Qed.

  Global Program Instance xist_sp : xistBI SPred :=
    fun T eqT mT cmT R =>
      mkSPred (fun n => exists t, R t n) _.
  Next Obligation.
    intros n m HLe [t HR]; exists t; rewrite HLe; apply HR.
  Qed.

  (* For some reason tc inference gets confused otherwise *)
  Existing Instance sp_type.

  (* All of the above preserve all the props it should. *)
  Global Instance and_sp_equiv : Proper (equiv ==> equiv ==> equiv) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.
  Global Instance and_sp_dist n : Proper (dist n ==> dist n ==> dist n) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; intros; (split; [apply EQP | apply EQQ]; now auto with arith).
  Qed.
  Global Instance and_sp_ord : Proper (pord ==> pord ==> pord) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.

  Global Instance or_sp_equiv : Proper (equiv ==> equiv ==> equiv) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.
  Global Instance or_sp_dist n : Proper (dist n ==> dist n ==> dist n) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; (intros [HP | HQ]; [left; apply EQP | right; apply EQQ]; now auto with arith).
  Qed.
  Global Instance or_sp_ord : Proper (pord ==> pord ==> pord) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.

  Global Instance impl_sp_equiv : Proper (equiv ==> equiv ==> equiv) impl_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    setoid_rewrite EQP; setoid_rewrite EQQ; tauto.
  Qed.
  Global Instance impl_sp_dist n : Proper (dist n ==> dist n ==> dist n) impl_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; intros; apply EQQ, H, EQP; now eauto with arith.
  Qed.
  Global Instance impl_sp_ord : Proper (pord --> pord ++> pord) impl_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n HP m r'.
    rewrite <- EQP, <- EQQ; now apply HP.
  Qed.

  Global Instance sc_sp_equiv : Proper (equiv ==> equiv ==> equiv) sc_sp := and_sp_equiv.
  Global Instance sc_sp_dist n : Proper (dist n ==> dist n ==> dist n) sc_sp := and_sp_dist n.
  Global Instance sc_sp_ord : Proper (pord ==> pord ==> pord) sc_sp := and_sp_ord.

  Global Instance si_sp_equiv : Proper (equiv ==> equiv ==> equiv) si_sp := impl_sp_equiv.
  Global Instance si_sp_dist n : Proper (dist n ==> dist n ==> dist n) si_sp := impl_sp_dist n.
  Global Instance si_sp_ord : Proper (pord --> pord ++> pord) si_sp := impl_sp_ord.

  Section Quantifiers.
    Context V `{pU : cmetric V}.

    Existing Instance nonexp_type.

    Global Instance all_sp_equiv : Proper (equiv (A := V -n> SPred) ==> equiv) all.
    Proof.
      intros R1 R2 EQR n; simpl.
      setoid_rewrite EQR; tauto.
    Qed.
    Global Instance all_sp_dist n : Proper (dist (T := V -n> SPred) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR m HLt; simpl.
      split; intros; apply EQR; now auto.
    Qed.

    Global Instance xist_sp_equiv : Proper (equiv (A := V -n> SPred) ==> equiv) xist.
    Proof.
      intros R1 R2 EQR n; simpl.
      setoid_rewrite EQR; tauto.
    Qed.
    Global Instance xist_sp_dist n : Proper (dist (T := V -n> SPred)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR m HLt; simpl.
      split; intros [t HR]; exists t; apply EQR; now auto.
    Qed.

  End Quantifiers.

  Global Program Instance bi_sp : ComplBI SPred.
  Next Obligation.
    intros n; simpl; tauto.
  Qed.
  Next Obligation.
    intros n [HP HQ]; assumption.
  Qed.
  Next Obligation.
    intros n [HP HQ]; assumption.
  Qed.
  Next Obligation.
    split; intros HH n.
    - intros HP m HLe HQ; apply HH; split; [rewrite HLe |]; assumption.
    - intros [HP HQ]; eapply HH; eassumption || reflexivity.
  Qed.
  Next Obligation.
    intros n HP; left; assumption.
  Qed.
  Next Obligation.
    intros n HQ; right; assumption.
  Qed.
  Next Obligation.
    intros n; simpl; tauto.
  Qed.
  Next Obligation.
    intros P Q n; simpl. tauto.
  Qed.
  Next Obligation.
    intros P Q R n; split; simpl; tauto.
  Qed.
  Next Obligation.
    intros n; split; simpl; tauto.
  Qed.
  Next Obligation.
    split; intros HH n; simpl in *.
    - intros HP m HLe HQ. apply HH. split; last assumption. rewrite HLe. assumption.
    - intros [HP HQ]. eapply HH; try eassumption; omega.
  Qed.
  Next Obligation.
    split.
    - intros HH n HP u; apply HH; assumption.
    - intros HH u n HP; apply HH; assumption.
  Qed.
  Next Obligation.
    intros n HA u; apply H, HA.
  Qed.
  Next Obligation.
    split.
    - intros HH n [u HP]; eapply HH; eassumption.
    - intros HH u n HP; apply HH; exists u; assumption.
  Qed.
  Next Obligation.
    intros n [[u HP] HQ]; exists u. split; assumption.
  Qed.
  Next Obligation.
    intros n [u HA]; exists u. apply H, HA.
  Qed.

End SPredBI.

Section SPredLater.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Global Instance later_sp_mon : Proper (pord ==> pord) later_sp.
  Proof.
    intros p q Hpq [| n]; [intros; exact I | simpl; apply Hpq].
  Qed.

  Global Program Instance later_spred : Later SPred :=
    Build_Later _ m[(later_sp)] _ _ _.
  Next Obligation.
    intros [| n] Ht; [exact I | simpl].
    rewrite Le.le_n_Sn; assumption.
  Qed.
  Next Obligation.
    intros n p q Hpq [| m] HLt; simpl; [tauto |].
    apply Hpq; auto with arith.
  Qed.
  Next Obligation.
    intros n _; induction n.
    - apply HL; exact I.
    - apply HL, IHn.
  Qed.

End SPredLater.



(* This class describes a type that can close over "future Us",
   thus making a nonexpansive map monotone *)
Class MonotoneClosure T `{pcmT : pcmType T} :=
  { mclose : forall {U} `{pcmU : pcmType U} {eU : extensible U},
               (U -n> T) -n> U -m> T;
    mclose_cl : forall {U} `{pcmU : pcmType U} {eU : extensible U} (f : U -n> T) u,
                  mclose f u ⊑ f u; (* RJ: TODO why can't we get rid of the eta-expanded u here? *)
    mclose_fw : forall {U} `{pcmU : pcmType U} {eU : extensible U} (f : U -n> T) u t
                       (HFW : forall u' (HS : u ⊑ u'), t ⊑ f u'),
                  t ⊑ mclose f u
  }.
Arguments Build_MonotoneClosure {_ _ _ _ _ _} _ {_ _}.

Section MonotoneExt.
  Context B `{BBI : ComplBI B} {MCB : MonotoneClosure B}
          T `{pcmT' : pcmType T} {eT : extensible T}.
  Local Obligation Tactic := intros; resp_set || mono_resp || eauto with typeclass_instances.

  Global Instance top_mm : topBI (T -m> B) := pcmconst top.
  Global Instance bot_mm : botBI (T -m> B) := pcmconst bot.

  (* TODO this should not depend on a full-blown BI for B *)
  Global Program Instance bounded_mm : Bounded (T -m> B).
  Next Obligation.
    intros t; apply top_true.
  Qed.
  Next Obligation.
    intros t; apply bot_false.
  Qed.


  Global Program Instance and_mm : andBI (T -m> B) :=
    fun P Q => m[(lift_bin and P Q)].
  Global Program Instance or_mm  : orBI  (T -m> B) :=
    fun P Q => m[(lift_bin or P Q)].

  Global Instance impl_mm : implBI (T -m> B) :=
    fun P Q => mclose (lift_bin impl P Q).

  Global Program Instance sc_mm  : scBI  (T -m> B) :=
    fun P Q => m[(lift_bin sc P Q)].

  Global Instance si_mm : siBI (T -m> B) :=
    fun P Q => mclose (lift_bin si P Q).

  Global Program Instance all_mm : allBI (T -m> B) :=
    fun U eqU mU cmU R =>
      m[(fun t => all n[(fun u => R u t)])].
  Next Obligation.
    intros t1 t2 EQt; apply all_dist; intros u; simpl morph.
    rewrite EQt; reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 Subt; apply all_pord; intros u; simpl morph.
    rewrite Subt; reflexivity.
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
    rewrite Subt; reflexivity.
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

  Global Instance impl_mm_equiv : Proper (equiv ==> equiv ==> equiv) impl_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; unfold impl_mm.
    apply (morph_resp mclose); intros t; simpl morph.
    apply impl_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance impl_mm_dist n : Proper (dist n ==> dist n ==> dist n) impl_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; apply met_morph_nonexp; intros t; simpl morph.
    apply impl_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance impl_mm_ord : Proper (pord --> pord ++> pord) impl_mm.
  Proof.
    intros P1 P2 SubP Q1 Q2 SubQ t; unfold flip in SubP; unfold impl, impl_mm.
    apply mclose_fw; intros t' Subt; rewrite Subt; clear t Subt; simpl morph.
    rewrite SubP, <- SubQ; apply mclose_cl.
  Qed.

  Global Instance sc_mm_equiv : Proper (equiv ==> equiv ==> equiv) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply sc_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_dist n : Proper (dist n ==> dist n ==> dist n) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply sc_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_ord : Proper (pord ==> pord ==> pord) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply sc_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance si_mm_equiv : Proper (equiv ==> equiv ==> equiv) si_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; apply (morph_resp mclose); intros t; simpl morph.
    apply si_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance si_mm_dist n : Proper (dist n ==> dist n ==> dist n) si_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; apply met_morph_nonexp; intros t; simpl morph.
    apply si_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance si_mm_ord : Proper (pord --> pord ++> pord) si_mm.
  Proof.
    intros P1 P2 SubP Q1 Q2 SubQ t; unfold flip in SubP; unfold impl, impl_mm.
    apply mclose_fw; intros t' Subt; rewrite Subt; clear t Subt; simpl morph.
    rewrite SubP, <- SubQ; apply mclose_cl.
  Qed.

  Section Quantifiers.
    Context V `{cmV : cmetric V}.

    Global Instance all_mm_equiv : Proper (equiv (A := V -n> T -m> B) ==> equiv) all.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply all_equiv; intros u; simpl morph; apply EQR.
    Qed.
    Global Instance all_mm_dist n : Proper (dist (T := V -n> T -m> B) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply all_dist; intros u; simpl morph; apply EQR.
    Qed.

    Global Instance xist_mm_equiv : Proper (equiv (A := V -n> T -m> B) ==> equiv) xist.
    Proof.
      intros R1 R2 EQR t; simpl.
      apply xist_equiv; intros u; simpl; apply EQR.
    Qed.
    Global Instance xist_mm_dist n : Proper (dist (T := V -n> T -m> B)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply xist_dist; intros u; simpl morph; apply EQR.
    Qed.

  End Quantifiers.

  Global Program Instance bi_mm : ComplBI (T -m> B).
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
      rewrite Subt, <- and_impl; assumption.
    - rewrite and_impl, (HH t); apply mclose_cl.
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
    intros f1 f2 t; simpl morph; apply comm.
  Qed.
  Next Obligation.
    intros f1 f2 f3 t; simpl morph; apply assoc.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply sc_top_unit.
  Qed.
  Next Obligation.
    split; intros HH t; simpl morph.
    - apply mclose_fw; intros t' Subt; specialize (HH t'); simpl morph in *.
      rewrite Subt, <- sc_si; assumption.
    - rewrite sc_si, (HH t); apply mclose_cl.
  Qed.
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- all_R; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *; rewrite <- all_R in HH.
      simpl morph in HH; apply HH.
  Qed.
  Next Obligation.
    intros t; apply all_pord; intros u; simpl morph; apply H.
  Qed.
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- xist_L; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *.
      rewrite <- xist_L in HH; simpl morph in HH; apply HH.
  Qed.
  Next Obligation.
    intros t; simpl morph.
    rewrite xist_sc; eapply xist_pord; intros u; simpl morph.
    reflexivity.
  Qed.
  Next Obligation.
    intros t; apply xist_pord; intros u; apply H.
  Qed.

End MonotoneExt.

Section MonotoneLater.
  Context B `{BBI : ComplBI B} {MCB : MonotoneClosure B} {LB: Later B}
          T `{pcmT' : pcmType T} {eT : extensible T}.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Global Program Instance later_mon_morph : Later (T -m> B) :=
    Build_Later (T -m> B) m[(fun f: T -m> B => m[(fun u => later (f u))])] _ _ _.
  Next Obligation.
    intros u; simpl morph; apply later_mon.
  Qed.
  Next Obligation.
    intros n f g Hfg u; simpl morph; apply later_contr, Hfg.
  Qed.
  Next Obligation.
    intros u; apply loeb, HL.
  Qed.

End MonotoneLater.

