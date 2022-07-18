(*************

Implementation of our work surrounding the concept of negotiation

Anna Fritz and Perry Alexander 


Thoughts (9/11/20)

- How do we take terms to capabilites?? 
  - where does the target keep the list of everything it can generate? 
  - Do we need some kind of function that could take a term (request) and 
    match all possible terms that could be generated? 
    

***************)

(*******************

Appraiser: goal is to verify the target is trustworthy 

Target: body that is appraised to determine trustworthiness 

Negotiation: the communication between the appraiser and target to determine the best protocol for attestation 

Privacy Policy: the policy that ensure the target or appraiser does not share sensitive information 

Selection Policy: a relation that maps concrete goals to abstract implementation


 ********************)


Require Import Poset.
Require Import Lattice.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.RelationClasses.

(* A place is the location where negotiation happens 
   Right now, a place describes who is participating 
   in the negotiation. *)

Definition Plc := nat.
Definition ASP_ID := nat. 


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


  (* A request is sent from appraiser to target. 
   The request is a term that describes the appraiser's
   desires for attestation. *)

Definition Request := Term. 

(*  The proposal is sent from target to appraiser. 
    It includes the terms the target is willing 
    to share during attestation. 

    In the proposal, there will either be one 
    term, or more than one term.  

    The top includes all possible terms in 
    the proposal and the bottom is no terms.*)

Definition Proposal := Ensemble Term.
Definition Top : Ensemble Term := Full_set Term. 
Definition Bottom : Ensemble Term := Empty_set Term. 

Theorem top_includes_all : forall t:Term, In Term (Top) t. 
 Proof. 
   intros.
   apply Full_intro.
 Qed.

Theorem bottom_includes_none : forall t:Term, ~(In Term (Empty_set Term) t). 
Proof.
  intros.
  intros not. 
  inversion not. 
Qed.

Module PosetEnsemble <: Poset.
  (* Module inherits from Poset which must prove 
     reflexivity, antisymmetry, and transitivity *)


  (* Equality for the Ensemble is defined if the two are the same set *)
  Definition t : Type := Ensemble Term.
  Definition eq (t1 t2 : t) : Prop := (Same_set _ t1 t2).

  Hint Unfold eq.
  
  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40). 

  Theorem eq_refl : forall x, x == x.
  Proof.
    unfold eq. intros. simpl. unfold Same_set.
    split; unfold Included; intros; apply H.
  Qed.
     
  Theorem eq_sym : forall x y, x == y -> y == x.
      Proof. intros x y. intros H. unfold eq. unfold Same_set. split; inversion H.
         + apply H1.
         + apply H0.
       Qed. 
           
  Theorem eq_trans : forall x y z,  x == y -> y == z -> x == z.
     Proof. intros x y z. intros H1 H2.
         unfold eq in *. unfold Same_set in *. inversion H1.  inversion H2. split.
            + unfold Included in H. unfold Included. intros.
              apply H in H5. unfold Included in H3. apply H3 in H5. apply H5.
            + unfold Included in H4. unfold Included. intros.
              apply H4 in H5. unfold Included in H0. apply H0 in H5. apply H5.
     Qed.

  (* Order implies one set of terms is greater than another set of terms. 
     So the set  with more elements is greater *)
  Definition order := Included Term. 
     
  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).
  
  Theorem order_refl : forall x y, x == y -> x <<= y.
  Proof.
    intros. unfold order. inversion H. apply H0. 
  Qed.
  
  Theorem order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Proof.
    intros; unfold order in *; unfold eq; unfold Same_set; split.
    apply H. apply H0.
  Qed.
  
  Theorem order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
  Proof.
    intros. 
    unfold order in *. 
    unfold Included in *. 
    intros. apply H0.  apply H. apply H1. 
  Qed. 

End PosetEnsemble.

Module Decidability.

  (* Two terms are decidable. *)
  
  Definition t_eq_dec : forall (x y : Term), {x = y} + {x <> y}. 
  Proof.
    repeat decide equality.
  Defined. 

  (* Either a term is in the proposal or not in the proposal *)
  Definition in_dec : forall (pr : Proposal) (t: Term),
      {pr t} + {~(pr t)} -> {In _ pr t} + {~(In _ pr t)}.
  Proof. 
    intros. inversion H.
    + left. apply H0.
    + right. apply H0. 
  Defined. 

  Check t_eq_dec (asp (HSH)) (asp (HSH)).

  (* Definition in_dec' :  forall (pr : Proposal) (t: Term),
      {pr t} + {~(pr t)} -> {In _ pr t} + {~(In _ pr t)}.
    refine (fix f (t : Term) (pr : Proposal) : {pr t} + {~(pr t)} -> {In _ pr t} + {~(In _ pr t)} :=
              match pr t with
              |
              |
              end. 
    intros. inversion H.
    + left. apply H0.
    + right. apply H0. 
  Defined. *)
  
End Decidability. 
  
  
   (* A record is defined to hold both the target's policies and 
   the appraiser's policies. 

   For the appraiser, the privacy policy takes the place (the details 
   of the appraiser) and the request to make sure the request does 
   not share confidentation information. It returns a True/False 
   to say if the request is okay. The selection policy takes a place
   and the proposal and chooses the best term from the proposal. 
   This will be the term used for attestation. 

   For the target, the privacy policy makes sure each term 
   in the proposal does not share any secret information. 
   It takes the target's description (place) and the proposal and 
   returns a subset satisfying the privacy policy. The selection policy
   for the target takes the place and the request and finds terms that
   satisfy the request and the privacy policy and places those 
   terms inside the proposal. The proposal is returned to the appraiser. *)

(* In Chlipala's TransitionSystems.v file, he uses Inductive definitions 
   to implement his record. However, his record must be recursive (not obviously possible)
   where our privacy policy doesn't need to be. *)

Record Tpolicy := {
                   T_selection : Plc -> Term -> Term -> Prop;
                   T_privacy : Plc -> Term -> Prop
                 }.

Record Apolicy := {
                   A_privacy : Plc -> Term -> Prop;
                   A_selection : Plc -> Term -> Proposal -> Term -> Prop
                 }.

Module VirusCheckerRelations.

  Import Decidability.
  
  (* Simplist example is to ask place 1 to return a hash of its virus checker *)
  Definition req1 := att 1 (asp (HSH)).   

  (* The appraiser's privacy policy must allow for the HSH request *)
  Inductive A_PP : Plc -> Term -> Prop :=
  | HSH_A_PP : forall (p : Plc) (t : Term), t = att 1 (asp HSH) -> A_PP p t. 

  (* This relation is the selection policy. Lets say the target selects any protocols with a HSH term  *)
  Inductive T_SP : Plc -> Term -> Term -> Prop :=
  | HSH1_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                (* pt1 *)
                                                t2 = att 1 (asp HSH) ->
                                                T_SP p t1 t2 
  | HSH2_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                (* pt2 *)
                                                t2 = lseq (att 1 (asp (HSH))) (asp (SIG)) ->
                                                T_SP p t1 t2
  | HSH3_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                (* pt3 *)
                                                t2 = lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG)) ->
                                                T_SP p t1 t2
  | HSH4_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                (* npt2 *)
                                                t2 = lseq (att 2 (asp (HSH))) (asp (SIG)) ->
                                                T_SP p t1 t2                                                 
  | HSH5_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                (* npt3 *)
                                                t2 = att 2 (asp HSH) ->
                                                T_SP p t1 t2. 
  
  (* Lets assume the target's privacy policy will only allow measuments from place 1 and place 0 *)
  Inductive T_PP : Plc -> Term -> Prop :=
  | PL0_T_PP : forall (p : Plc) (t1 t2 : Term), t1 = (att 0 (t2)) -> T_PP p t1
  | PL1_T_PP : forall (p : Plc) (t1 t2 : Term), t1 = (att 1 (t2)) -> T_PP p t1. 

  
  (* The appraiser looks at the proposal and selects the "best term"
     Here, best is the one that matches most closely to the request. *)
  Inductive A_SP : Plc -> Term -> Proposal -> Term -> Prop :=
  | HSH1_A_SP : forall (pl : Plc) (pr : Proposal) (r t2: Term),  r = att 1 (asp HSH) ->
                                                                 pr = Add _ (Add _ (Singleton _  (att 1 (asp (HSH))))
                                                                          (lseq (att 1 (asp (HSH))) (asp (SIG))))
                                                                          (lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG))) ->
                                                                 t2 = att 1 (asp HSH) ->
                                                                 A_SP pl r pr t2.
  
  (* We situationally define the privacy policy and the selection policy for the 
     target an appraiser by implementing an instance of the record. *)
  Definition t_1 : Tpolicy := {|
                                T_privacy := T_PP;
                                T_selection := T_SP
                              |}.

  Definition a_1 : Apolicy := {|
                               A_privacy := A_PP;
                               A_selection := A_SP
                             |}.
    
End VirusCheckerRelations.

Module VirusCheckFunction. 

  Import VirusCheckerRelations. 

  Check req1. 
  (*att 1 (asp (HSH))*) 


  (* The terms are everything that is possible from the data structure *)

  Definition terms := Term.
  Definition capabilities := Term.

  (* capabilites are a set *)
  Check capabilities.

  (* The capabilites are all possible terms the target can generate *)

  (* Here are the possible terms (pt) the target sends in the proposal
     c1 returns the Copland phrase to hash the virus checker
     c2 asks place 1 to return a signed hash of the virus checker 
     c3 ensures freshness by introducing a nonce that becomes inital evidence 
         passed to the @1 term where the nonce evidence is sent to CPY and 
         the USM measures a hash of the virus checker 
     c4 should not be selected as it doesnt fulfill the request 
     c5-c6 violate the target's privacy policy. The target cannot 
           send information about place 2. 
   *)

  (* Do i want capabilites to be an inductive structure then? *)


  Inductive cap' : Set :=
  |  c1' : cap'.

   Inductive cap'' : Term -> Prop :=
   | c1'' : cap'' (att 1 (asp (HSH)))
   | c2'' : cap'' (lseq (att 1 (asp (HSH))) (asp (SIG)))
   | c3'' : cap'' (lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG)))
   | c4'' : cap'' (att 1 (asp (ASPC 1)))
   | c5'' : cap'' (lseq (att 2 (asp (HSH))) (asp (SIG)))
   | c6'' : cap'' (att 2 (asp HSH)).

   Check cap''. 

   

   (*Now I dont think you can combine terms in the cap'' in an ensemble *)
  
  Definition c1 := att 1 (asp (HSH)).
  Definition c2 := lseq (att 1 (asp (HSH))) (asp (SIG)).
  Definition c3 := lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG)).
  Definition c4 := (att 1 (asp (ASPC 1))).
  Definition c5 := lseq (att 2 (asp (HSH))) (asp (SIG)).
  Definition c6 := att 2 (asp HSH). 

  Definition cap_set (r:Request) : Ensemble capabilities :=
    match r with
    | att 1 (asp (HSH)) =>  (Add _ (Add _  (Add _ (Add _ (Add _ (Singleton _ c1'') c2'') c3'') c4'') c5'') c6'')
    | _ => Bottom
    end.

  (* Next, we need to turn capabilites into selectable terms 
     This is where we get rid of c6 
   *)

   Definition select_set (c : Term) : Ensemble Term :=
    match c with
    | att 1 (asp (HSH)) =>  (Singleton _ c1)
    | c2 => Bottom
    | c3 => Bottom 
    end.
  
  
  (* This definition uses subset types to say 
     the only term that fits the definition is KIM 3*)
  Definition privacy_sub : {t:term | t = (KIM 3)}. 
  Proof.
    econstructor. reflexivity. 
  Qed.
                                    








