(* Copland terms, events, and annotated terms *)

(* LICENSE NOTICE
Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.
This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This module contains the basic definitions for Copland terms,
    events, and annotated terms. *)

Require Import Omega Preamble.

    (** * Terms and Evidence
        A term is either an atomic ASP, a remote call, a sequence of terms
        with data a dependency, a sequence of terms with no data
        dependency, or parallel terms. *)
    
    (** [Plc] represents a place. *)
    
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
(* | KIM: ASP_ID -> Plc -> (list Arg) -> ASP *)
| ASPC: ASP_ID (* -> (list Arg) *) -> ASP
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
(*| sp: SP -> Evidence -> Evidence *)
(* | kk: ASP_ID -> Plc -> Plc -> (list Arg) -> Evidence -> Evidence *)
| uu: ASP_ID -> Plc -> (* (list Arg) -> *) Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: Plc -> N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.