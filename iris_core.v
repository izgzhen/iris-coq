Require Import ssreflect.
Require Import world_prop core_lang.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

(* Because Coq has a restriction of how to apply functors, we have to hack a bit here.
   The hack that involves least work, is to duplicate the definition of our final
   resource type, as a module type (which is how we can use it, circumventing the
   Coq restrictions) and as a module (to show the type can be instantiated). *)
Module Type IRIS_RES (RL : RA_T) (C : CORE_LANG) <: RA_T.
  Instance state_type : Setoid C.state := discreteType.

  Definition res := (ex C.state * RL.res)%type.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.

  (* The order on (ra_pos res) is inferred correctly, but this one is not *)
  Instance res_pord: preoType res := ra_preo (T := res).
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

  Instance Props_BI : ComplBI Props | 0 := _.
  Instance Props_Later : Later Props | 0 := _.

  Implicit Types (P Q : Props) (w : Wld) (n i k : nat) (r u v : res) (σ : state).

  (* Simple view lemmas. *)

  Lemma lerefl (n : nat) : n <= n. Proof. by reflexivity. Qed.

  Lemma lelt {n k} (H : k < n) : k <= n.
  Proof. by omega. Qed.

  Lemma lt0 (n : nat) :  ~ n < 0. Proof. by omega. Qed.

  Lemma propsMW {P w n r w'} (HSw : w ⊑ w') : P w n r -> P w' n r.
  Proof. exact: (mu_mono _ _ P _ _ HSw). Qed.

  Lemma propsMNR {P w n r n' r'} (HLe : n' <= n) (HSr : r ⊑ r') : P w n r -> P w n' r'.
  Proof. exact: (uni_pred _ _ _ _ _ HLe HSr). Qed.

  Lemma propsMN {P w n r n'} (HLe : n' <= n) : P w n r -> P w n' r.
  Proof. apply: (propsMNR HLe (prefl r)). Qed.

  Lemma propsMR {P w n r r'} (HSr : r ⊑ r') : P w n r -> P w n r'.
  Proof. exact: (propsMNR (lerefl n) HSr). Qed.

  Lemma propsM {P w n r w' n' r'} (HSw : w ⊑ w') (HLe : n' <= n) (HSr : r ⊑ r') :
    P w n r -> P w' n' r'.
  Proof. move=> HP; by apply: (propsMW HSw); exact: (propsMNR HLe HSr). Qed.

  Lemma propsMWR {P w n r w' r'} (HLe : w ⊑ w') (HSr : r ⊑ r') : P w n r -> P w' n r'.
  Proof. move=> HP; eapply propsM; (eassumption || reflexivity). Qed.

  Lemma propsMWN {P w n r w' n'} (HSw : w ⊑ w') (HLe : n' <= n) :
    P w n r -> P w' n' r.
  Proof. move=> HP; eapply propsM; (eassumption || reflexivity). Qed.


  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Resources.

    Lemma state_sep {σ g rf} (Hv : ↓(ex_own σ, g) · rf) : fst rf == 1.
    Proof. move: (ra_sep_prod Hv) => [Hs _]; exact: ra_sep_ex Hs. Qed.

    Lemma state_fps {σ g σ' rf} (Hv : ↓(ex_own σ, g) · rf) : ↓(ex_own σ', g) · rf.
    Proof. exact: (ra_fps_fst (ra_fps_ex σ σ') rf). Qed.

  End Resources.

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        for any UPred over a RA. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

    Program Definition box : Props -n> Props :=
      n[(fun P => m[(fun w => mkUPred (fun n r => P w n 1) _)])].
    Next Obligation.
      intros n m r s HLe _ Hp; rewrite-> HLe; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw m r HLt; simpl.
      eapply (met_morph_nonexp _ _ P); eassumption.
    Qed.
    Next Obligation.
      intros w1 w2 Subw n r; simpl.
      apply P; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w m r HLt; simpl.
      apply EQp; assumption.
    Qed.

    Global Program Instance box_dist n : Proper (dist n ==> dist n) box.
    Next Obligation.
      move=> P P' HEq w k r HLt.
      exact: (HEq w).
    Qed.

  End Necessitation.

  Notation "□ P" := (box P) (at level 30, right associativity) : iris_scope.

  (** Lemmas about box **)
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
      exact: (met_morph_nonexp _ _ φ).
    Qed.

    Lemma box_all : □all φ == box_all_lhs.
    Proof. done. Qed.
  End BoxAll.

  (** "Internal" equality **)
  Section IntEq.
    Context {T} `{mT : metric T}.

    Program Definition intEqP (t1 t2 : T) : UPred res :=
      mkUPred (fun n r => t1 = S n = t2) _.
    Next Obligation.
      intros n1 n2 _ _ HLe _; apply mono_dist; omega.
    Qed.

    Instance subrel_dist_n `{mT : metric T} (n m: nat) (Hlt: m < n) : subrelation (dist n) (dist m).
    Proof.
      intros x y HEq. eapply mono_dist, HEq. omega.
    Qed.

    Program Definition intEq: T -n> T -n> Props :=
      n[(fun t1 => n[(fun t2 => pcmconst (intEqP t1 t2))])].
    Next Obligation.
      intros t2 t2' Heqt2. intros w m r HLt.
      change ((t1 = S m = t2) <-> (t1 = S m = t2')). (* Why, oh why... *)
      split; (etransitivity; [eassumption|]); eapply mono_dist; (eassumption || symmetry; eassumption).
    Qed.
    Next Obligation.
      intros t1 t1' Heqt1. intros t2 w m r HLt.
      change ((t1 = S m = t2) <-> (t1' = S m = t2)). (* Why, oh why... *)
      split; (etransitivity; [|eassumption]); eapply mono_dist; (eassumption || symmetry; eassumption).
    Qed.

  End IntEq.

  Notation "t1 '===' t2" := (intEq t1 t2) (at level 70) : iris_scope.

  Notation "P ↔ Q" := ((P → Q) ∧ (Q → P)) (at level 95, no associativity) : iris_scope.

  Lemma biimpL {P Q : Props} {w n r} : (P ↔ Q) w n r -> (P → Q) w n r.
  Proof. by move=>[L _]. Qed.

  Lemma biimpR {P Q : Props} {w n r} : (P ↔ Q) w n r -> (Q → P) w n r.
  Proof. by move=>[_ R]. Qed.

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

    Goal forall P Q, (P ↔ Q) ⊑ (P === Q).
    Proof.
      move=> P Q w n r [Hpq Hqp] w' n' r' HLt; split.
      move=> HP.	(* Lacking w ⊑ w', we cannot apply Hpq. *)
    Abort.

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
      - symmetry in EQw; assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
        apply (met_morph_nonexp _ _ P) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
      - assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
        apply (met_morph_nonexp _ _ P) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
    Qed.
    Next Obligation.
      intros w1 w2 HSw n; simpl; intros _ HT w' m r HSw' HLt Hp.
      eapply HT, Hp; [etransitivity |]; eassumption.
    Qed.

  End Timeless.

  Section IntEqTimeless.
    Context {T} `{tT: Setoid T}.
    (* This only works for types with the discrete metric! *)
    Local Instance mT: metric T := discreteMetric.

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
    (* We define this on *any* resource, not just the positive (valid) ones.
       Note that this makes ownR trivially *False* for invalid u: There is no
       element v such that u · v = r (where r is valid) *)
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

  Lemma valid_iff P :
    valid P <-> (⊤ ⊑ P).
  Proof.
    split; intros Hp.
    - intros w n r _; apply Hp.
    - intros w n r; apply Hp; exact I.
  Qed.

End IRIS_CORE.

Module IrisCore (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) : IRIS_CORE RL C R WP.
  Include IRIS_CORE RL C R WP.
End IrisCore.
