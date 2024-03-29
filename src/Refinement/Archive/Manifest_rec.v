
(*************
This file was the first attempt at the manifest (6.28.22). It uses record types. There is great discription in here about ASPs and the goal of the local and global manifests.  
*)
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

(* Require Import Term_Defs Example_Phrases_Admits.*) 
Require Import Coq.Relations.Relation_Definitions. 
Require Import String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.

(*********************
COPLAND GRAMMAR 
Had to redefine the Copland grammar below in order to write some examples. 
**********************)

Inductive Plc: Set := 
| relyingParty
| attester
| appraiser.

Theorem eq_plc (x y : Plc): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Definition N_ID: Set := nat.

Definition Event_ID: Set := nat.

Inductive ASP_ID : Set := 
| attest_id : ASP_ID
| encrypt :  ASP_ID
| decrypt :  ASP_ID. 

Inductive TARG_ID: Set := 
| o1 : TARG_ID 
| o2 : TARG_ID.

Inductive Arg: Set := 
| a_pub_key : Arg 
| t_priv_key : Arg 
| t_pub_key : Arg. 

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive Evidence: Set :=
| mt: Evidence
| uu: (*ASP_PARAMS ->*) ASP_PARAMS ->
      (*Evidence ->*) Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP.

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

(*  ******************
    UNDERSTANDING ASPs
    ******************

    ASPs are attestation service providers. They are typically located at the attester and are measurement tools that perform atomic measurements or consume evidence. 

    An example of calling an ASP would be with the phrase "@1 (vc p t)" where the virus checker is an ASP that is to take measurement of t at place p. The @1 represents the measuring place. 

    This leads me to believe that we need to caputure the place that can preform measurement, the ASP used, the place the ASP can measure, and the target of measurement. Therefore, the ASP constructor is composed of the asp_id, t_place, and target. 

    To do this, we can use the ASP structure as defined in "Term_Defs.v" where ASPC cna be used to capture the previously mentioned variables.
    *)

  Print ASP. 

(* **************
   DEFINING MANIFEST
   **************  

   Need to take into consideration 
   - keys/ids 
      * capture by defining a platform (an attestation manager lives on a platform)
   - list of ASPs 
      * This can be more summed up as the "capabilities" of the ASP. IE that they can measure certain targets at certain places. Need the measuring place to indicate where the ASP is located.
   - Measures relation
      * describes who can measure what 
   - Context 
      * what does it need to run
      * what does it have around it to run  *)
   
Record localMAN : Set := mkLOCAL 
{ lPlatform : Plc ; 
  lASP : (list ASP) }. 
   
(* manifest will not have *)
Record globalMAN : Set := mkGLOBAL
{ gLOCAL : list localMAN
  (* gM : inhabited (relation Plc) *)}.

(***************************
  DEFINING GENERATE FUNCTION 
  ***************************

  Once the manifest is written, we need some way to generate a list of protocols that can be used for attestation.  

  First, `generate` is the entry point to the function. This turns the manifest into a list of INI files. Next, `generate_list` function called the generate_from_ini for each element in the INI file. generate_from_ini is the fundamental operation as it actually generates the protocols. *)

Fixpoint generate_from_ini (p : Plc ) (a : list ASP) : list Term := 
  match a with 
  | nil => nil 
  | cons h t => match h with 
                | CPY => [att p ( asp CPY) ] ++ generate_from_ini p t
                | HSH => [att p ( asp HSH) ] ++ generate_from_ini p t
                | SIG => [att p ( asp SIG) ] ++ generate_from_ini p t
                | ASPC (asp_paramsC a l tp tar) => [att p (asp (ASPC (asp_paramsC a l tp tar)))] ++ generate_from_ini p t
                end
  end.

Fixpoint generate_list (m: list localMAN) : list Term :=
  match m with 
  | (nil)  => [ ]
  | (cons h t') => generate_from_ini h.(lPlatform) h.(lASP) ++ generate_list t'
  end. 

Definition generate (m : globalMAN) : list Term := 
  match m.(gLOCAL) with 
   | nil => []
   | list => generate_list list 
  end.

(* all terms can be produced via the generate function *)
Lemma generate_ok : forall (t:Term) (m:globalMAN),  m.(gLOCAL) <> nil ->  In t (generate m).
Proof.
Abort.

(***************************
  DEFINING COMBINATION FUNCTION 
  At some point, we need to look at how protocols are combined. If they can be joined in sequence or parallel. Perhaps use a lattice to model this then walking the lattice will give you different possible combinations of terms. 
  ***************************)

(****************************
  TARGET'S SELECTION POLICY
  We want to be able to pass in a reqest, and recieve a list of terms that satisfy the reqest. First, use generate to recieve a list of protocols. Then string matching to return all protocols that include the requested protocol. 
*****************************)  

Definition eq_targ_id : forall x y : TARG_ID, {x = y} + {x <> y}.
Proof.
  intros. repeat decide equality.
Defined.

Check eq_targ_id. 

(* what to do about copying, signing, or hashing??? 

this only works with bool. What kind of type is prop?? why doesn't this work with Prop?? *)

(** match_r_t take in the request and the term from the global manifest. It returns the boolean true if the request is present in the term and false if not. *)

Fixpoint match_r_t (r : TARG_ID) (t: Term) : bool := 
  match t with 
  | asp (ASPC (asp_paramsC _ _ _ tar)) => if (eq_targ_id r tar) then true else false
  | asp _ => false
  | att p t' => match_r_t r t'
  | lseq t1 t2 => match_r_t r t1 || match_r_t r t2
  | bseq _ t1 t2 => match_r_t r t1 || match_r_t r t2
  | bpar _ t1 t2 => match_r_t r t1 || match_r_t r t2
  end. 


(* The selection function. This using select_r_t to generate a list of terms that satisfy the request. *)
Fixpoint select_t (r: TARG_ID) (t_in : list Term) (t_out : list Term) : list Term := 
match t_in with 
| (cons h t) => if (match_r_t r h)
                then select_t r t ([h] ++ t_out) 
                else select_t r t (t_out)
| _ => t_out
end.


(*****************************
  PRIVACY POLICY
******************************)


(******************************
    THE NEGOTIATE FUNCTION 
    Here we take the request and the target's manifest to actually generate a list of protocols. 
  *****************************)
Definition negotiate_t (r: TARG_ID) (m :globalMAN) : list Term :=
  select_t r (generate m) []. 
    

(******************************
  THEORIES  
  Here we come to our main Theorem. This says, forall terms generated through negotation are actually in the Manifest. Essentially, can the manifest run the selected protocols? 
******************************)

(***************************
  DEFINING EXECUATABLE FUNCTION 

  To check if any phrase is executable, check to see if it is in the Manifest. 
  *************************** *)

  Definition hasASP (k: Plc) (gm: globalMAN) (a:ASP) : Prop :=
    match gm.(gLOCAL) with 
    | nil => False 
    | _ => False
    end.


(***************************
   EXAMPLE 

   Assumer ther are two places (attestation managers). Place 1 (P1) and place 2 (P2).  They each have an ASP "attest" which takes a measurement of the system. 

   Say that P0, the relying party, requests an attestation of P1.
   
   Request = "o1" 
****************************)
 
(* the relying party formulates the request. The request is for an attestation to measure target o1. *)
Definition request := TARG_ID.
Definition r1 : request := o1. 

(* this is the ini file for the attester. Assume the attester has two places: place 1 and place 2. Each take the "attest" measurement of the system. *)
Definition loc_man1 := mkLOCAL 1 [ASPC (asp_paramsC attest_id [] 1 o1)].
Definition loc_man2 := mkLOCAL 2 [ASPC (asp_paramsC attest_id [] 2 o2)].

Definition glob_man := mkGLOBAL [loc_man1 ; loc_man2].
Print glob_man.

(* Now, we have defined global and local manifest. We can look at what happens once request is sent. *)

(* request is sent to attester. Target needs to call "generate" function where a manifest is input and outputs some protocols. Then target needs to call thier selection function. Finally, will need to call a privacy funtion.  *)

Definition gen : list Term := generate (glob_man).
Definition sel : list Term := select_t r1 gen []. 
Compute gen. 
Compute sel.

(* Future step: privacy policy. *)
(* DESIGN DECISION : do we want the privacy policy to consider ASPs or copland protocols? *)
