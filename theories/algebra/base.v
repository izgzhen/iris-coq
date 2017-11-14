From Coq.ssr Require Export ssreflect.
From stdpp Require Export prelude.
Set Default Proof Using "Type".
Global Open Scope general_if_scope.
Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.
