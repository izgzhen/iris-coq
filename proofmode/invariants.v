From iris.proofmode Require Export tactics pviewshifts.
From iris.program_logic Require Export invariants.
From iris.proofmode Require Import coq_tactics intro_patterns.

Tactic Notation "iInvCore" constr(N) "as" tactic(tac) constr(Hclose) :=
  let Htmp := iFresh in
  let patback := intro_pat.parse_one Hclose in
  let pat := constr:(IList [[IName Htmp; patback]]) in
  iVs (inv_open _ N with "[#]") as pat;
    [idtac|iAssumption || fail "iInv: invariant" N "not found"|idtac];
    [solve_ndisj || match goal with |- ?P => fail "iInv: cannot solve" P end
    |tac Htmp].

Tactic Notation "iInv" constr(N) "as" constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2 x3) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2 x3 x4) pat) Hclose.
