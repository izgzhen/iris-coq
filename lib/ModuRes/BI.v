Require Import PreoMet.
Require Import RA.

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

  Class ComplBI `{pcmT : pcmType T, BIT : topBI, BIB : botBI, BIA : andBI,
                                    BIO : orBI, BII : implBI, BISC : scBI, BISI : siBI}
        {BIAll : allBI} {BIXist : xistBI} :=
    mkCBI {
        top_true    :  forall P, P ⊑ top;
        bot_false   :  forall P, bot ⊑ P;
        and_self    :  forall P, P ⊑ and P P;
        and_projL   :  forall P Q, and P Q ⊑ P;
        and_projR   :  forall P Q, and P Q ⊑ Q;
        and_equiv   :> Proper (equiv ==> equiv ==> equiv) and;
        and_dist n  :> Proper (dist n ==> dist n ==> dist n) and;
        and_pord    :> Proper (pord ==> pord ==> pord) and;
        and_impl    :  forall P Q R, and P Q ⊑ R <-> P ⊑ impl Q R;
        impl_equiv  :> Proper (equiv ==> equiv ==> equiv) impl;
        impl_dist n :> Proper (dist n ==> dist n ==> dist n) impl;
        impl_pord   :> Proper (pord --> pord ++> pord) impl;
        or_injL     :  forall P Q, P ⊑ or P Q;
        or_injR     :  forall P Q, Q ⊑ or P Q;
        or_self     :  forall P, or P P ⊑ P;
        or_equiv    :> Proper (equiv ==> equiv ==> equiv) or;
        or_dist n   :> Proper (dist n ==> dist n ==> dist n) or;
        or_pord     :> Proper (pord ==> pord ==> pord) or;
        sc_comm     :> Commutative sc;
        sc_assoc    :> Associative sc;
        sc_top_unit :  forall P, sc top P == P;
        sc_equiv    :> Proper (equiv ==> equiv ==> equiv) sc;
        sc_dist n   :> Proper (dist n ==> dist n ==> dist n) sc;
        sc_pord     :> Proper (pord ==> pord ==> pord) sc;
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
        xist_sc    U `{cmU : cmetric U} :
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
Arguments ComplBI T {_ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Class Valid (T : Type) `{pcmT : pcmType T} :=
  { valid : T -> Prop;
    valid_top (t t' : T) (HV : valid t) : t' ⊑ t
  }.

Class Later (T : Type) `{pcmT : pcmType T} {vT : Valid T} :=
  { later : T -m> T;
    later_mon (t : T) : t ⊑ later t;
    later_contr : contractive later;
    loeb (t : T) (HL : later t ⊑ t) : valid t
  }.

Delimit Scope bi_scope with bi.
Notation " ▹ p " := (later p) (at level 20) : bi_scope.
Notation "⊤" := (top) : bi_scope.
Notation "⊥" := (bot) : bi_scope.
Notation "p ∧ q" := (and p q) (at level 40, left associativity) : bi_scope.
Notation "p ∨ q" := (or p q) (at level 50, left associativity) : bi_scope.
Notation "p * q" := (sc p q) (at level 40, left associativity) : bi_scope.
Notation "p → q" := (impl p q) (at level 55, right associativity) : bi_scope.
Notation "p '-*' q" := (si p q) (at level 55, right associativity) : bi_scope.
Notation "∀ x , p" := (all n[(fun x => p)]) (at level 60, x ident, no associativity) : bi_scope.
Notation "∃ x , p" := (xist n[(fun x => p)]) (at level 60, x ident, no associativity) : bi_scope.
Notation "∀ x : T , p" := (all n[(fun x : T => p)]) (at level 60, x ident, no associativity) : bi_scope.
Notation "∃ x : T , p" := (xist n[(fun x : T => p)]) (at level 60, x ident, no associativity) : bi_scope.

Require Import UPred.

Section UPredLater.
  Context Res `{preoRes : preoType Res}.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Global Program Instance valid_up : Valid (UPred Res) :=
    Build_Valid _ _ _ _ _ _ (fun p : UPred Res => forall n r, p n r) _.
  Next Obligation.
    intros n r _; apply HV.
  Qed.

  Global Instance later_up_mon : Proper (pord ==> pord) later_up.
  Proof.
    intros p q Hpq [| n] r; [intros; exact I | simpl; apply Hpq].
  Qed.

  Global Program Instance later_upred : Later (UPred Res) :=
    Build_Later _ _ _ _ _ _ _ m[(later_up)] _ _ _.
  Next Obligation.
    intros [| n] r Ht; [exact I | simpl].
    rewrite Le.le_n_Sn; assumption.
  Qed.
  Next Obligation.
    intros n p q Hpq [| m] r HLt; simpl; [tauto |].
    apply Hpq; auto with arith.
  Qed.
  Next Obligation.
    intros n r; induction n.
    - apply HL; exact I.
    - apply HL, IHn.
  Qed.

End UPredLater.

Section UPredBI.
  Context res `{raRes : RA res}.
  Local Open Scope ra_scope.
  Local Obligation Tactic := intros; eauto with typeclass_instances.

  (* Standard interpretations of propositional connectives. *)
  Global Program Instance top_up : topBI (UPred res) := up_cr (const True).
  Global Program Instance bot_up : botBI (UPred res) := up_cr (const False).

  Global Program Instance and_up : andBI (UPred res) :=
    fun P Q =>
      mkUPred (fun n r => P n r /\ Q n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSub; rewrite HSub, HLe; tauto.
  Qed.
  Global Program Instance or_up : orBI (UPred res) :=
    fun P Q =>
      mkUPred (fun n r => P n r \/ Q n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSub; rewrite HSub, HLe; tauto.
  Qed.

  Global Program Instance impl_up : implBI (UPred res) :=
    fun P Q =>
      mkUPred (fun n r => forall m r', m <= n -> r ⊑ r' -> P m r' -> Q m r') _.
  Next Obligation.
    intros n m r1 r2 HLe HSub HImp k r3 HLe' HSub' HP.
    apply HImp; try (etransitivity; eassumption); assumption.
  Qed.
  
  (* BI connectives. *)
  Global Program Instance sc_up : scBI (UPred res) :=
    fun P Q =>
      mkUPred (fun n r => exists r1 r2, r1 · r2 == r /\ P n r1 /\ Q n r2) _.
  Next Obligation.
    intros n m r1 r2 HLe [rd HEq] [r11 [r12 [HEq' [HP HQ]]]].
    rewrite <- HEq', assoc in HEq; setoid_rewrite HLe.
    exists (rd · r11).
    exists r12.
    split; [|split;[|assumption] ].
    - simpl. assumption.
    - eapply uni_pred, HP; [reflexivity|].
      exists rd. reflexivity.
  Qed.

  Global Program Instance si_up : siBI (UPred res) :=
    fun P Q =>
      mkUPred (fun n r => forall m r' rr, r · r' == rr -> m <= n -> P m r' -> Q m rr) _.
  Next Obligation.
    intros n m r1 r2 HLe [r12 HEq] HSI k r rr HEq' HSub HP.
    rewrite comm in HEq; rewrite <- HEq, <- assoc in HEq'.
    pose (rc := (r12 · r)).
    eapply HSI with (r':=rc); [| etransitivity; eassumption |].
    - simpl. assumption. 
    - eapply uni_pred, HP; [reflexivity|]. exists r12. reflexivity.
  Qed.

  (* Quantifiers. *)
  Global Program Instance all_up : allBI (UPred res) :=
    fun T eqT mT cmT R =>
      mkUPred (fun n r => forall t, R t n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSub HR t; rewrite HLe, <- HSub; apply HR.
  Qed.

  Global Program Instance xist_up : xistBI (UPred res) :=
    fun T eqT mT cmT R =>
      mkUPred (fun n r => exists t, R t n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSub [t HR]; exists t; rewrite HLe, <- HSub; apply HR.
  Qed.

  (* For some reason tc inference gets confused otherwise *)
  Existing Instance up_type.

  (* All of the above preserve all the props it should. *)
  Global Instance and_up_equiv : Proper (equiv ==> equiv ==> equiv) and_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.
  Global Instance and_up_dist n : Proper (dist n ==> dist n ==> dist n) and_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m r HLt; simpl.
    split; intros; (split; [apply EQP | apply EQQ]; now auto with arith).
  Qed.
  Global Instance and_up_ord : Proper (pord ==> pord ==> pord) and_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.

  Global Instance or_up_equiv : Proper (equiv ==> equiv ==> equiv) or_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.
  Global Instance or_up_dist n : Proper (dist n ==> dist n ==> dist n) or_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m r HLt; simpl.
    split; (intros [HP | HQ]; [left; apply EQP | right; apply EQQ]; now auto with arith).
  Qed.
  Global Instance or_up_ord : Proper (pord ==> pord ==> pord) or_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    rewrite EQP, EQQ; tauto.
  Qed.

  Global Instance impl_up_equiv : Proper (equiv ==> equiv ==> equiv) impl_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    setoid_rewrite EQP; setoid_rewrite EQQ; tauto.
  Qed.
  Global Instance impl_up_dist n : Proper (dist n ==> dist n ==> dist n) impl_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m r HLt; simpl.
    split; intros; apply EQQ, H0, EQP; now eauto with arith.
  Qed.
  Global Instance impl_up_ord : Proper (pord --> pord ++> pord) impl_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r HP m r'.
    rewrite <- EQP, <- EQQ; apply HP.
  Qed.

  Global Instance sc_up_equiv : Proper (equiv ==> equiv ==> equiv) sc_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    setoid_rewrite EQP; setoid_rewrite EQQ; tauto.
  Qed.
  Global Instance sc_up_dist n : Proper (dist n ==> dist n ==> dist n) sc_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m r HLt; simpl.
    split; intros [r1 [r2 [EQr [HP HQ]]]]; exists r1; exists r2;
    (split; [assumption | split; [apply EQP | apply EQQ]; now auto with arith]).
  Qed.
  Global Instance sc_up_ord : Proper (pord ==> pord ==> pord) sc_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r HH; simpl.
    setoid_rewrite <- EQP; setoid_rewrite <- EQQ; apply HH.
  Qed.

  Global Instance si_up_equiv : Proper (equiv ==> equiv ==> equiv) si_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r; simpl.
    setoid_rewrite EQP; setoid_rewrite EQQ; tauto.
  Qed.
  Global Instance si_up_dist n : Proper (dist n ==> dist n ==> dist n) si_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m r HLt; simpl.
    split; intros; eapply EQQ, H0, EQP; now eauto with arith.
  Qed.
  Global Instance si_up_ord : Proper (pord --> pord ++> pord) si_up.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n r HP m r' rr.
    rewrite <- EQP, <- EQQ; apply HP.
  Qed.

  Section Quantifiers.
    Context V `{pU : cmetric V}.

    Existing Instance nonexp_type.

    Global Instance all_up_equiv : Proper (equiv (A := V -n> UPred res) ==> equiv) all.
    Proof.
      intros R1 R2 EQR n r; simpl.
      setoid_rewrite EQR; tauto.
    Qed.
    Global Instance all_up_dist n : Proper (dist (T := V -n> UPred res) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR m r HLt; simpl.
      split; intros; apply EQR; now auto.
    Qed.

    Global Instance xist_up_equiv : Proper (equiv (A := V -n> UPred res) ==> equiv) xist.
    Proof.
      intros R1 R2 EQR n r; simpl.
      setoid_rewrite EQR; tauto.
    Qed.
    Global Instance xist_up_dist n : Proper (dist (T := V -n> UPred res)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR m r HLt; simpl.
      split; intros [t HR]; exists t; apply EQR; now auto.
    Qed.

  End Quantifiers.

  Global Program Instance bi_up : ComplBI (UPred res).
  Next Obligation.
    intros n r _; exact I.
  Qed.
  Next Obligation.
    intros n r HC; contradiction HC.
  Qed.
  Next Obligation.
    intros n r; simpl; tauto.
  Qed.
  Next Obligation.
    intros n r [HP HQ]; assumption.
  Qed.
  Next Obligation.
    intros n r [HP HQ]; assumption.
  Qed.
  Next Obligation.
    split; intros HH n r.
    - intros HP m r' HLe HSub HQ; apply HH; split; [rewrite HLe, <- HSub |]; assumption.
    - intros [HP HQ]; eapply HH; eassumption || reflexivity.
  Qed.
  Next Obligation.
    intros n r HP; left; assumption.
  Qed.
  Next Obligation.
    intros n r HQ; right; assumption.
  Qed.
  Next Obligation.
    intros n r; simpl; tauto.
  Qed.
  Next Obligation.
    intros P Q n r; simpl.
    split; intros [r1 [r2 HPQ]]; exists r2 r1; rewrite comm; tauto.
  Qed.
  Next Obligation.
    intros P Q R n r; split.
    - intros [r1 [rr [EQr [HP [r2 [r3 [EQrr [HQ HR]]]]]]]].
      rewrite <- EQrr, assoc in EQr. unfold sc.
      exists (r1 · r2).
      exists r3; split; [assumption | split; [| assumption] ].
      exists r1 r2; split; [reflexivity | split; assumption].
    - intros [rr [r3 [EQr [[r1 [r2 [EQrr [HP HQ]]]] HR]]]].
      rewrite <- EQrr, <- assoc in EQr; clear EQrr.
      exists r1.
      exists (r2 · r3).
      split; [assumption | split; [assumption |] ].
      exists r2 r3; split; [reflexivity | split; assumption].
  Qed.
  Next Obligation.
    intros n r; split.
    - intros [r1 [r2 [EQr [_ HP]]]].
      eapply uni_pred, HP; [reflexivity|]. exists (r1). assumption.
    - intros HP. exists (ra_unit res) r. split; [simpl; erewrite ra_op_unit by apply _; reflexivity |].
      simpl; unfold const; tauto.
  Qed.
  Next Obligation.
    split; intros HH n r.
    - intros HP m r' rr EQrr HLe HQ; apply HH; rewrite <- HLe in HP.
      eexists; eexists; split; [eassumption | tauto].
    - intros [r1 [r2 [EQr [HP HQ]]]]; eapply HH; eassumption || reflexivity.
  Qed.
  Next Obligation.
    split.
    - intros HH n r HP u; apply HH; assumption.
    - intros HH u n r HP; apply HH; assumption.
  Qed.
  Next Obligation.
    intros n r HA u; apply H0, HA.
  Qed.
  Next Obligation.
    split.
    - intros HH n r [u HP]; eapply HH; eassumption.
    - intros HH u n r HP; apply HH; exists u; assumption.
  Qed.
  Next Obligation.
    intros n t [t1 [t2 [EQt [[u HP] HQ]]]]; exists u t1 t2; tauto.
  Qed.
  Next Obligation.
    intros n r [u HA]; exists u; apply H0, HA.
  Qed.

End UPredBI.

(* This class describes a type that can close over "future Us",
   thus making a nonexpansive map monotone *)
Class MonotoneClosure T `{pcmT : pcmType T} :=
  { mclose : forall {U} `{pcmU : pcmType U} {eU : extensible U},
               (U -n> T) -n> U -m> T;
    mclose_cl : forall {U} `{pcmU : pcmType U} {eU : extensible U} (f : U -n> T) u,
                  mclose f u ⊑ f u;
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
    intros t; apply top_true.
  Qed.
  Next Obligation.
    intros t; apply bot_false.
  Qed.
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
  Context T U `{LT : Later T} `{pcmU : pcmType U}.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Global Program Instance valid_mon : Valid (U -m> T) :=
    Build_Valid _ _ _ _ _ _ (fun f : U -m> T => forall u, valid (f u)) _.
  Next Obligation.
    intros u; apply valid_top, HV.
  Qed.

  Global Program Instance later_mon_morph : Later (U -m> T) :=
    Build_Later _ _ _ _ _ _ _ m[(fun f => m[(fun u => later (f u))])] _ _ _.
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

Section MComplUP.

  Context V `{pV : preoType V}.
  Local Obligation Tactic := intros; try resp_set.

  Section Def.
    Context T `{pcmT : pcmType T} {eT : extensible T}.

    Program Definition mclose_up : (T -n> UPred V) -n> T -m> UPred V :=
      n[(fun f => m[(fun t => mkUPred (fun n v => forall t', t ⊑ t' -> f t' n v) _)])].
    Next Obligation.
      intros n m v1 v2 HLe HSubv HT t' HSubt.
      rewrite HLe, <- HSubv; apply HT, HSubt.
    Qed.
    Next Obligation.
      intros t1 t2 EQt m v HLt; split; intros HT t' Subt;
      (destruct n as [| n]; [now inversion HLt |]).
      - symmetry in EQt.
        assert (HH : f t' = S n = f (extend t' t1)) by (eapply f, extend_dist; eassumption).
        apply HH; [assumption |].
        eapply HT, extend_sub; eassumption.
      - assert (HH : f t' = S n = f (extend t' t2)) by (eapply f, extend_dist; eassumption).
        apply HH; [assumption |].
        eapply HT, extend_sub; eassumption.
    Qed.
    Next Obligation.
      intros t1 t2 Subt n v HT t' Subt'; apply HT; etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros f1 f2 EQf u m v HLt; split; intros HH u' HSub; apply EQf, HH; assumption.
    Qed.

  End Def.

  Global Program Instance MCl_up : MonotoneClosure (UPred V) :=
    Build_MonotoneClosure mclose_up.
  Next Obligation.
    intros n v HH; apply HH; reflexivity.
  Qed.
  Next Obligation.
    intros n v HH u' HSub; apply HFW; assumption.
  Qed.

End MComplUP.

(* The above suffice for showing that the eqn used in Iris actually forms a Complete BI.
   The following would allow for further monotone morphisms to be added. *)

Section MComplMM.
  Context B `{BBI : ComplBI B} {MCB : MonotoneClosure B}
          V `{pcmV : pcmType V} {eT : extensible V}.
  Local Obligation Tactic := intros; resp_set || mono_resp || eauto with typeclass_instances.

  Section Def.
    Context U `{pcmU : pcmType U} {eU : extensible U}.

    Program Instance extensible_prod : extensible (U * V) :=
      mkExtend (fun uv1 uv2 => (extend (fst uv1) (fst uv2), extend (snd uv1) (snd uv2))).
    Next Obligation.
      destruct vd as [ud vd]; destruct ve as [ue ve].
      destruct HD as [HDu HDv]; destruct HS as [HSu HSv].
      split; eapply extend_dist; eassumption.
    Qed.
    Next Obligation.
      destruct vd as [ud vd]; destruct ve as [ue ve].
      destruct HD as [HDu HDv]; destruct HS as [HSu HSv].
      split; eapply extend_sub; eassumption.
    Qed.

    Program Definition mclose_mm : (U -n> V -m> B) -n> U -m> V -m> B :=
      n[(fun f => mcurry (mclose n[(fun uv => f (fst uv) (snd uv))]))].
    Next Obligation.
      intros [u1 v1] [u2 v2] [EQu EQv]; simpl morph.
      unfold fst, snd in *; rewrite EQu, EQv; reflexivity.
    Qed.
    Next Obligation.
      intros f1 f2 EQf u v; simpl morph.
      apply mclose; clear u v; intros [u v]; simpl morph.
      apply EQf.
    Qed.

  End Def.

  Global Program Instance MCl_mm : MonotoneClosure (V -m> B) := Build_MonotoneClosure mclose_mm.
  Next Obligation.
    intros v; simpl morph.
    rewrite mclose_cl; reflexivity.
  Qed.
  Next Obligation.
    intros v; simpl morph.
    apply mclose_fw; intros [u' v'] [HSubu HSubv]; simpl morph.
    rewrite HSubv; apply HFW; assumption.
  Qed.

End MComplMM.

Section BIValid.
  Local Obligation Tactic := intros.

  Global Program Instance BI_valid T `{ComplBI T} : Valid T :=
    Build_Valid _ _ _ _ _ _ (fun t => top ⊑ t) _.
  Next Obligation.
    etransitivity; [apply top_true | assumption].
  Qed.

End BIValid.
