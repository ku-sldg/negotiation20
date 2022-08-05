(* terms definition as taken from MITRE *)

Notation Plc := nat (only parsing).
    
    (** An argument to a userspace or kernel measurement. *)
    (* Notation Arg := nat (only parsing). *)
Notation ASP_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
    
    (*
    Definition eq_arg_dec:
      forall x y: Arg, {x = y} + {x <> y}.
    Proof.
      intros;
      decide equality; decide equality.
    Defined.
    Hint Resolve eq_arg_dec.
    *)
    
Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_ID -> ASP
| SIG: ASP
| HSH: ASP.
    
    (** The method by which data is split is specified by a natural number. *)
    
Inductive SP: Set :=
| ALL
| NONE.
    
Definition Split: Set := (SP * SP).
    
Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term                            
| bseq: Split -> Term -> Term -> Term 
| bpar: Split -> Term -> Term -> Term.

Inductive Evidence: Set :=
| mt: Evidence
| uu: ASP_ID -> Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: Plc -> N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.
