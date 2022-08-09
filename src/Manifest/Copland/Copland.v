Require Import Lists.List.
Import ListNotations.
Require Import String.

Module Copland.

Module Term.
  
Definition Plc: Set := string.
Definition N_ID: Set := nat.
Definition Event_ID: Set := nat.
Definition ASP_ID: Set := string.
Definition TARG_ID: Set := string.
Definition Arg: Set := string.

Notation plc_dec := string_dec.

(** The structure of evidence. *)

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive Evidence: Set :=
| mt: Evidence
| nn: N_ID -> Evidence
| gg: Plc -> ASP_PARAMS -> Evidence -> Evidence
| hh: Plc -> ASP_PARAMS -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence.
Theorem Evidence_dec : forall a1 a2 : Evidence, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Inductive SP: Set :=
| ALL
| NONE.
Theorem SP_dec : forall a1 a2 : SP, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Inductive FWD: Set :=
| COMP
| EXTD.
Theorem FWD_dec : forall a1 a2 : FWD, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Inductive ASP: Set :=
| NULL: ASP
| CPY: ASP
| ASPC: SP -> FWD -> ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP.
Theorem ASP_dec : forall a1 a2 : ASP, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Definition Split: Set := (SP * SP).

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.
Theorem Term_dec : forall a1 a2 : Term, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

End Term.

End Copland.
