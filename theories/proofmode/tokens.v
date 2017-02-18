From stdpp Require Export strings.
Set Default Proof Using "Type".

Inductive token :=
  | TName : string → token
  | TAnom : token
  | TFrame : token
  | TBar : token
  | TBracketL : token
  | TBracketR : token
  | TAmp : token
  | TParenL : token
  | TParenR : token
  | TBraceL : token
  | TBraceR : token
  | TPure : token
  | TAlways : token
  | TModal : token
  | TPureIntro : token
  | TAlwaysIntro : token
  | TModalIntro : token
  | TSimpl : token
  | TForall : token
  | TAll : token
  | TMinus : token
  | TSep : token.

Fixpoint cons_name (kn : string) (k : list token) : list token :=
  match kn with "" => k | _ => TName (string_rev kn) :: k end.
Fixpoint tokenize_go (s : string) (k : list token) (kn : string) : list token :=
  match s with
  | "" => reverse (cons_name kn k)
  | String "?" s => tokenize_go s (TAnom :: cons_name kn k) ""
  | String "$" s => tokenize_go s (TFrame :: cons_name kn k) ""
  | String "[" s => tokenize_go s (TBracketL :: cons_name kn k) ""
  | String "]" s => tokenize_go s (TBracketR :: cons_name kn k) ""
  | String "|" s => tokenize_go s (TBar :: cons_name kn k) ""
  | String "(" s => tokenize_go s (TParenL :: cons_name kn k) ""
  | String ")" s => tokenize_go s (TParenR :: cons_name kn k) ""
  | String "&" s => tokenize_go s (TAmp :: cons_name kn k) ""
  | String "{" s => tokenize_go s (TBraceL :: cons_name kn k) ""
  | String "}" s => tokenize_go s (TBraceR :: cons_name kn k) ""
  | String "%" s => tokenize_go s (TPure :: cons_name kn k) ""
  | String "#" s => tokenize_go s (TAlways :: cons_name kn k) ""
  | String ">" s => tokenize_go s (TModal :: cons_name kn k) ""
  | String "!" (String "%" s) => tokenize_go s (TPureIntro :: cons_name kn k) ""
  | String "!" (String "#" s) => tokenize_go s (TAlwaysIntro :: cons_name kn k) ""
  | String "!" (String ">" s) => tokenize_go s (TModalIntro :: cons_name kn k) ""
  | String "/" (String "=" s) => tokenize_go s (TSimpl :: cons_name kn k) ""
  | String "*" (String "*" s) => tokenize_go s (TAll :: cons_name kn k) ""
  | String "*" s => tokenize_go s (TForall :: cons_name kn k) ""
  | String "-" s => tokenize_go s (TMinus :: cons_name kn k) ""
  | String (Ascii.Ascii false true false false false true true true) (* unicode ∗ *)
      (String (Ascii.Ascii false false false true false false false true)
      (String (Ascii.Ascii true true true false true false false true) s)) =>
     tokenize_go s (TSep :: cons_name kn k) ""
  | String a s =>
     if is_space a then tokenize_go s (cons_name kn k) ""
     else tokenize_go s k (String a kn)
  (* TODO: Complain about invalid characters, to future-proof this
  against making more characters special. *)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".
