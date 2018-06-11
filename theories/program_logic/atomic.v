From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics classes.
From iris.bi.lib Require Export atomic.
From iris.bi Require Import telescopes.
Set Default Proof Using "Type".

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else. *)
Definition atomic_wp `{irisG Λ Σ} {TA TB : tele}
  (e: expr Λ) (* expression *)
  (Eo : coPset) (* (outer) mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (f: TA → TB → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    (∀ Q (Φ : val Λ → iProp Σ), Q -∗
             atomic_update Eo ∅ α β (λ.. x y, Q -∗ Φ (f x y)) -∗
             WP e {{ Φ }})%I.
(* Note: To add a private postcondition, use
   atomic_update α β Eo Ei (λ x y, POST x y -∗ Φ (f x y)) *)

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. )
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : stdpp_scope.

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             e%E
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) β%I
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) v%V
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : stdpp_scope.

Notation "'<<<' α '>>>' e @ Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. ))
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. ))
  )
  (at level 20, Eo, α, β, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : stdpp_scope.

Notation "'<<<' α '>>>' e @ Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             e%E
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) v%V)
  )
  (at level 20, Eo, α, β, v at level 200,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<'  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : stdpp_scope.
