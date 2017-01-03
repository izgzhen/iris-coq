From iris.prelude Require Export strings.
Set Default Proof Using "Type*".

Inductive sel_pat :=
  | SelPure
  | SelPersistent
  | SelSpatial
  | SelName : string → sel_pat.

Fixpoint sel_pat_pure (ps : list sel_pat) : bool :=
  match ps with
  | [] => false
  | SelPure :: ps => true
  | _ :: ps => sel_pat_pure ps
  end.

Module sel_pat.
Fixpoint cons_name (kn : string) (k : list sel_pat) : list sel_pat :=
  match kn with "" => k | _ => SelName (string_rev kn) :: k end.

Fixpoint parse_go (s : string) (k : list sel_pat) (kn : string) : list sel_pat :=
  match s with
  | "" => rev (cons_name kn k)
  | String "%" s => parse_go s (SelPure :: cons_name kn k) ""
  | String "#" s => parse_go s (SelPersistent :: cons_name kn k) ""
  | String (Ascii.Ascii false true false false false true true true) (* unicode ∗ *)
      (String (Ascii.Ascii false false false true false false false true)
      (String (Ascii.Ascii true true true false true false false true) s)) =>
     parse_go s (SelSpatial :: cons_name kn k) ""
  | String a s =>
     if is_space a then parse_go s (cons_name kn k) ""
     else parse_go s k (String a kn)
  end.
Definition parse (s : string) : list sel_pat := parse_go s [] "".

Ltac parse s :=
  lazymatch type of s with
  | list sel_pat => s
  | list string => eval vm_compute in (SelName <$> s)
  | string => eval vm_compute in (parse s)
  end.
End sel_pat.
