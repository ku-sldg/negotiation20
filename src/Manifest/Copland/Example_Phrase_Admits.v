
(* File taken from Adam Petz on 9.2.22 

    Can get file to compile using 
        coqc -Q . Cop Example_Phrase_Admits.v       *)
From Cop Require Export Copland.
Import Copland.Term.

Definition attest_id : ASP_ID.
Admitted.

Definition appraise_id : ASP_ID.
Admitted.

Definition cert_id : ASP_ID.
Admitted.

Definition cache_id : ASP_ID.
Admitted.
(*
Definition store_id : ASP_ID.
Admitted.
Definition retrieve_id : ASP_ID.
Admitted.
*)



Definition store_args : list Arg.
Admitted.

Definition retrieve_args : list Arg.
Admitted.



Definition sys : TARG_ID.
Admitted.

Definition cache : TARG_ID.
Admitted.

Definition att_tid : TARG_ID.
Admitted.

Definition it : TARG_ID.
Admitted.