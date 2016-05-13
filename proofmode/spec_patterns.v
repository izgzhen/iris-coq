From iris.prelude Require Export strings.

Inductive spec_pat :=
  | SAssert : bool → list string → spec_pat
  | SPersistent : spec_pat
  | SPure : spec_pat
  | SAlways : spec_pat
  | SName : string → spec_pat
  | SForall : spec_pat.

Module spec_pat.
Inductive token :=
  | TName : string → token
  | TMinus : token
  | TBracketL : token
  | TBracketR : token
  | TPersistent : token
  | TPure : token
  | TAlways : token
  | TForall : token.

Fixpoint cons_name (kn : string) (k : list token) : list token :=
  match kn with "" => k | _ => TName (string_rev kn) :: k end.
Fixpoint tokenize_go (s : string) (k : list token) (kn : string) : list token :=
  match s with
  | "" => rev (cons_name kn k)
  | String " " s => tokenize_go s (cons_name kn k) ""
  | String "-" s => tokenize_go s (TMinus :: cons_name kn k) ""
  | String "[" s => tokenize_go s (TBracketL :: cons_name kn k) ""
  | String "]" s => tokenize_go s (TBracketR :: cons_name kn k) ""
  | String "#" s => tokenize_go s (TPersistent :: cons_name kn k) ""
  | String "%" s => tokenize_go s (TPure :: cons_name kn k) ""
  | String "!" s => tokenize_go s (TAlways :: cons_name kn k) ""
  | String "*" s => tokenize_go s (TForall :: cons_name kn k) ""
  | String a s => tokenize_go s k (String a kn)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".

Fixpoint parse_go (ts : list token) (g : option (bool * list string))
    (k : list spec_pat) : option (list spec_pat) :=
  match g with
  | None =>
     match ts with
     | [] => Some (rev k)
     | TName s :: ts => parse_go ts None (SName s :: k)
     | TMinus :: TBracketL :: ts => parse_go ts (Some (true,[])) k
     | TMinus :: ts => parse_go ts None (SAssert true [] :: k)
     | TBracketL :: ts => parse_go ts (Some (false,[])) k
     | TAlways :: ts => parse_go ts None (SAlways :: k)
     | TPersistent :: ts => parse_go ts None (SPersistent :: k)
     | TPure :: ts => parse_go ts None (SPure :: k)
     | TForall :: ts => parse_go ts None (SForall :: k)
     | _ => None
     end
  | Some (b, ss) =>
     match ts with
     | TName s :: ts => parse_go ts (Some (b,s :: ss)) k
     | TBracketR :: ts => parse_go ts None (SAssert b (rev ss) :: k)
     | _ => None
     end
  end.
Definition parse (s : string) : option (list spec_pat) :=
  parse_go (tokenize s) None [].

Ltac parse s :=
  lazymatch type of s with
  | list spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some ?pats => pats | _ => fail "invalid list spec_pat" s
              end
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some [?pat] => pat | _ => fail "invalid spec_pat" s
              end
  end.
End spec_pat.