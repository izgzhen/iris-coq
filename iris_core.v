Require Import Ssreflect.ssreflect Omega.
Require Import world_prop core_lang.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.Agreement.

Set Bullet Behavior "Strict Subproofs".

(* We hack a bit here to avoid spelling out module types for functor results.
   The hack that involves least work is to duplicate the definition of our final
   resource type as a module type (which is how we can use it, circumventing the
   Coq restrictions) and as a module (to show the type can be instantiated). *)
Module Type IRIS_RES (RL : RA_T) (C : CORE_LANG) <: RA_T.
  Instance state_type : Setoid C.state := discreteType.

  Definition res := (ex C.state * RL.res)%type.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.

  (* Make this explicit. It may otherwise use the order on pairs. *)
  Instance res_pord: preoType res := pord_ra.
End IRIS_RES.
Module IrisRes (RL : RA_T) (C : CORE_LANG) <: IRIS_RES RL C.
  Include IRIS_RES RL C. (* I cannot believe Coq lets me do this... *)
End IrisRes.

(* This instantiates the framework(s) provided by ModuRes to obtain a higher-order
   separation logic with ownership, later, necessitation and equality.
   The logic has "worlds" in its model, but nothing here uses them yet. *)
Module Type IRIS_CORE (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R).
  Export C.
  Export R.
  Export WP.

  Delimit Scope iris_scope with iris.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (** Instances for a bunch of types (some don't even have Setoids) *)
  Instance state_metr : metric state := discreteMetric.
  Instance state_cmetr : cmetric state := discreteCMetric.

  Instance logR_metr : metric RL.res := discreteMetric.
  Instance logR_cmetr : cmetric RL.res := discreteCMetric.

  Instance nat_type : Setoid nat := discreteType.
  Instance nat_metr : metric nat := discreteMetric.
  Instance nat_cmetr : cmetric nat := discreteCMetric.

  Instance expr_type : Setoid expr := discreteType.
  Instance expr_metr : metric expr := discreteMetric.
  Instance expr_cmetr : cmetric expr := discreteCMetric.

  (* We use this type quite a bit, so give it and its instances names *)
  Definition vPred := value -n> Props.
  Instance vPred_type  : Setoid vPred  := _.
  Instance vPred_metr  : metric vPred  := _.
  Instance vPred_cmetr : cmetric vPred := _.


  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)

  
  Instance Props_BI : BI Props | 0 := _.
  Instance Props_CBI : ComplBI Props | 0 := _.
  Instance Props_Eq : EqBI Props | 0 := _.

  Implicit Types (P Q : Props) (w : Wld) (n i k : nat) (r u v : res) (σ : state).

  (* Simple view lemmas. *)

  Section Views.
    Lemma lelt {n k} (H : k < n) : k <= n.
    Proof. by omega. Qed.

    Lemma lt0 (n : nat) :  ~ n < 0. Proof. by omega. Qed.

    Lemma propsMW {P w n w'} (HSw : w ⊑ w') : P w n -> P w' n.
    Proof. exact: (mu_mono P HSw). Qed.

    Lemma propsMN {P w n n'} (HLe : n' <= n) : P w n -> P w n'.
    Proof. apply: dpred HLe. Qed.

    Lemma propsM {P w n w' n' } (HSw : w ⊑ w') (HLe : n' <= n) :
      P w n -> P w' n'.
    Proof.
      move=> HP. eapply propsMW, propsMN, HP; assumption.
    Qed.

    Lemma biimpL {P Q : Props} {w n} : (P ↔ Q) w n -> (P → Q) w n.
    Proof. by move=>[L _]. Qed.

    Lemma biimpR {P Q : Props} {w n} : (P ↔ Q) w n -> (Q → P) w n.
    Proof. by move=>[_ R]. Qed.

    Lemma applyImpl {P Q: Props} {w n w' n'} (HImpl: (P → Q) w n) (HSw : w ⊑ w') (HLe : n' <= n):
      P w' n' -> Q w' n'.
    Proof.
      move=>HP. destruct HSw as [wF EQw]. rewrite <-EQw. rewrite comm. eapply HImpl; first assumption.
      simpl morph. by rewrite comm EQw.
    Qed.
  End Views.

  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Resources.

    Lemma state_sep {σ g rf} (Hv : ↓(ex_own σ, g) · rf) : fst rf == 1.
    Proof. move: (ra_sep_prod Hv) => [Hs _]; exact: ra_sep_ex Hs. Qed.

    Lemma state_fps {σ g σ' rf} (Hv : ↓(ex_own σ, g) · rf) : ↓(ex_own σ', g) · rf.
    Proof. exact: (ra_fps_fst (ra_fps_ex σ σ') rf). Qed.

  End Resources.

  Section Later.
    (** Note: this could be moved to BI, since it's possible to define
        more generally. However, we should first figure out a concise
        set of axioms. **)
    Program Definition later: Props -> Props :=
      fun P => m[(fun w => later_sp (P w))].
    Next Obligation.
      move=>w1 w2 EQw. simpl. eapply later_sp_dist. rewrite EQw. reflexivity.
    Qed.
    Next Obligation.
      move=>w1 w2 Hw n H. destruct n as [|n]; first exact I.
      simpl. rewrite <-Hw. exact H.
    Qed.

    Global Instance later_contractive: contractive later.
    Proof.
      move=>n P Q EQ w. rewrite/later. simpl morph. eapply contr.
      rewrite EQ. reflexivity.
    Qed.

    Global Instance later_dist n : Proper (dist n ==> dist n) later.
    Proof.
      pose (lf := contractive_nonexp later _).
      move=> ? ? ?.
        by apply: (met_morph_nonexp lf).
    Qed.    
  End Later.
  Notation " ▹ p " := (later p) (at level 35) : iris_scope.


  Section LaterProps.
    Lemma later_mon P: P ⊑ ▹P.
    Proof.
      move=>w n H. simpl morph.
      destruct n as [|n]; first exact I.
      simpl. eapply dpred; last eassumption. omega.
    Qed.

    Lemma loeb t (HL: later t ⊑ t): valid t.
      intros w n. induction n.
      - eapply HL. exact I.
      - eapply HL. exact IHn.
    Qed.

    Lemma later_true: (⊤:Props) == ▹⊤.
    Proof.
      move=> w n.
      case:n=>[|n].
      - reflexivity.
      - reflexivity.
    Qed.

    Lemma laterM {P Q: Props}:
      (P → Q) ∧ ▹P ⊑ ▹Q.
    Proof.
      move=>w0 n0 [HPQ HLP].
      destruct n0 as [|n0]; first by auto.
      simpl. simpl in HLP. eapply (applyImpl HPQ);[reflexivity|now eauto|assumption].
    Qed.

  End LaterProps.

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        more generally. However, we should first figure out a concise
        set of axioms. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

    Program Definition box : Props -n> Props :=
      n[(fun P => m[(fun w => mkUPred (fun n r => P w n 1) _)])].
    Next Obligation.
      intros n m r s HLe _ Hp; rewrite-> HLe; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw m r HLt; simpl.
      eapply (met_morph_nonexp P); eassumption.
    Qed.
    Next Obligation.
      intros w1 w2 Subw n r; simpl.
      apply P; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w m r HLt; simpl.
      apply EQp; assumption.
    Qed.

  End Necessitation.

  Notation "□ P" := (box P) (at level 35, right associativity) : iris_scope.

  (** Lemmas about box **)
  Section NecessitationProps.
    Lemma box_intro P Q (Hpr : □P ⊑ Q) :
      □P ⊑ □Q.
    Proof.
      intros w n r Hp; simpl; apply Hpr, Hp.
    Qed.

    Lemma box_elim P :
      □P ⊑ P.
    Proof.
      intros w n r Hp; simpl in Hp.
      eapply uni_pred, Hp; [reflexivity |].
      now eapply unit_min.
    Qed.

    Lemma box_top : ⊤ == □⊤.
    Proof.
      intros w n r; simpl; unfold const; reflexivity.
    Qed.

    Lemma box_disj P Q :
      □(P ∨ Q) == □P ∨ □Q.
    Proof.
      intros w n r; reflexivity.
    Qed.

    Lemma box_dup P :
      □P == □P * □P.
    Proof.
      intros w n r. split.
      - intros HP. exists 1 r. split; [now rewrite ra_op_unit|].
        split;  assumption.
      - intros [r1 [r2 [_ [HP _]]]]. assumption.
    Qed.

    Section BoxAll.
      Context {T} `{cT : cmetric T}.
      Context (φ : T -n> Props).

      Program Definition box_all_lhs : Props := ∀t, □φ t.
      Next Obligation.
        move=> t t' HEq.
        apply: box_dist.
        exact: (met_morph_nonexp φ).
      Qed.

      Lemma box_all : □all φ == box_all_lhs.
      Proof. done. Qed.
    End BoxAll.
  End NecessitationProps.

  Section IntEqProps.

    (* On Props, valid biimplication, valid internal equality, and external equality coincide. *)


    Remark valid_biimp_intEq {P Q} : valid(P ↔ Q) -> valid(P === Q).
    Proof.
      move=> H wz nz rz w n r HLt. move/(_ w n r): H => [Hpq Hqp]. split.
      - by move/(_ _ (prefl w) _ _ (lerefl n) (prefl r)): Hpq.
      - by move/(_ _ (prefl w) _ _ (lerefl n) (prefl r)): Hqp.
    Qed.

    Remark valid_intEq_equiv {P Q} : valid(P === Q) -> P == Q.
    Proof. move=> H w n r; exact: H. Qed.

    Remark valid_equiv_biimp {P Q} : P == Q -> valid(P ↔ Q).
    Proof.
      by move=> H wz nz rz; split; move=> w HSw n r HLe HSr; move: H->.
    Qed.

    (* Internal equality implies biimplication, but not vice versa. *)

    Remark biimp_equiv {P Q}: P === Q ⊑ (P ↔ Q).
    Proof.
      have HLt n n' : n' <= n -> n' < S n by omega.
      move=> w n r H; split;
      move=> w' HSw' n' r' HLe' HSr' HP;
      move/(_ w' n' r' (HLt _ _ HLe')): H => [Hpq Hqp];
      [exact: Hpq | exact: Hqp].
    Qed.

    (* Note that (P ↔ Q) ⊑ (P === Q) does NOT hold: The first says
       that the equivalence holds in all future worlds, the second says
       it holds in *all* worlds. *)

  End IntEqProps.

  Section Timeless.

    Definition timelessP P w n :=
      forall w' k r (HSw : w ⊑ w') (HLt : k < n) (Hp : P w' k r), P w' (S k) r.

    Program Definition timeless P : Props :=
      m[(fun w => mkUPred (fun n r => timelessP P w n) _)].
    Next Obligation.
      intros n1 n2 _ _ HLe _ HT w' k r HSw HLt Hp; eapply HT, Hp; [eassumption |].
      omega.
    Qed.
    Next Obligation.
      intros w1 w2 EQw k; simpl; intros _ HLt; destruct n as [| n]; [now inversion HLt |].
      split; intros HT w' m r HSw HLt' Hp.
      - symmetry in EQw; assert (HD := extend_dist EQw HSw); assert (HS := extend_sub EQw HSw).
        apply (met_morph_nonexp P) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
      - assert (HD := extend_dist EQw HSw); assert (HS := extend_sub EQw HSw).
        apply (met_morph_nonexp P) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
    Qed.
    Next Obligation.
      intros w1 w2 HSw n; simpl; intros _ HT w' m r HSw' HLt Hp.
      eapply HT, Hp; [etransitivity |]; eassumption.
    Qed.

  End Timeless.

  Section IntEqTimeless.
    Context {T} `{tT: Setoid T}.
    (* This only works for types with the discrete metric! *)
    Existing Instance discreteMetric.

    Lemma intEqTimeless (t1 t2: T):
      valid(timeless(intEq t1 t2)).
    Proof.
      intros w n r. intros w' k r' Hsq Hlt.
      simpl. tauto.
    Qed.
  End IntEqTimeless.

  Section Ownership.

    (* Make sure equiv is not simplified too soon. Unfortunately, settings this globally breaks
       other things. *)
    Local Arguments equiv {_ _} _ _ /.

    (** Ownership **)
    Program Definition ownR: res -=> Props :=
      s[(fun u => pcmconst (mkUPred(fun n r => u ⊑ r) _) )].
    Next Obligation.
      intros n m r1 r2 Hle [d Hd ] [e He]. change (u ⊑ r2). rewrite <-Hd, <-He.
      exists (d · e). rewrite assoc. reflexivity.
    Qed.
    Next Obligation.
      intros u1 u2 Hequ. intros w n r. split; intros [t Heqt]; exists t; [rewrite <-Hequ|rewrite Hequ]; assumption.
    Qed.

    Lemma ownR_timeless {u} :
      valid(timeless(ownR u)).
    Proof. intros w n _ w' k r _ _; now auto. Qed.

    Lemma ownR_sc u v:
      ownR (u · v) == ownR u * ownR v.
    Proof.
      intros w n r; split; [intros Hut | intros [r1 [r2 [EQr [Hu Ht] ] ] ] ].
      - destruct Hut as [s Heq]. rewrite-> assoc in Heq.
        exists (s · u) v.
        split; [|split].
        + rewrite <-Heq. reflexivity.
        + exists s. reflexivity.
        + do 13 red. reflexivity.
      - destruct Hu as [u' Hequ]. destruct Ht as [t' Heqt].
        exists (u' · t'). rewrite <-EQr, <-Hequ, <-Heqt.
        rewrite !assoc. eapply ra_op_proper; try (reflexivity || now apply _).
        rewrite <-assoc, (comm _ u), assoc. reflexivity.
    Qed.

    (** Proper physical state: ownership of the machine state **)
    Program Definition ownS : state -n> Props :=
      n[(fun σ => ownR (ex_own σ, 1))].
    Next Obligation.
      intros r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
      rewrite EQr. reflexivity.
    Qed.

    Lemma ownS_timeless {σ} : valid(timeless(ownS σ)).
    Proof. exact ownR_timeless. Qed.

    Lemma ownS_state {σ w n r} (Hv : ↓r) :
      (ownS σ) w n r -> fst r == ex_own σ.
    Proof.
      move: Hv; move: r => [rx _] [Hv _] [ [x _] /= [Hr _] ].
      move: Hv; rewrite -Hr {Hr}.
      by case: x.
    Qed.

    (** Proper ghost state: ownership of logical **)
    Program Definition ownL : RL.res -n> Props :=
      n[(fun r : RL.res => ownR (1, r))].
    Next Obligation.
      intros r1 r2 EQr. destruct n as [| n]; [apply dist_bound |eapply dist_refl].
      simpl in EQr. intros w m t. simpl. change ( (ex_unit, r1) ⊑ t <->  (ex_unit, r2) ⊑ t). rewrite EQr. reflexivity.
    Qed.

    Lemma ownL_timeless {r : RL.res} : valid(timeless(ownL r)).
    Proof. exact ownR_timeless. Qed.

    (** Ghost state ownership **)
    Lemma ownL_sc (r s : RL.res) :
      ownL (r · s) == ownL r * ownL s.
    Proof.
      assert (Heq: (1, r · s) == ((1, r) · (1, s)) ) by reflexivity.
      (* I cannot believe I have to write this... *)
      change (ownR (1, r · s) == ownR (1, r) * ownR (1, s)).
      rewrite Heq.
      now eapply ownR_sc.
    Qed.

  End Ownership.

  (* People will need that *)
  Definition wf_nat_ind := well_founded_induction Wf_nat.lt_wf.

End IRIS_CORE.

Module IrisCore (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) : IRIS_CORE RL C R WP.
  Include IRIS_CORE RL C R WP.
End IrisCore.
