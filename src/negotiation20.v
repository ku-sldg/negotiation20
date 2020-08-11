(*************

Implementation of our work surrounding the concept of negotiation

Anna Fritz and Perry Alexander 


Thoughts (7/30) 
- We now have an ordering of terms based on length (the 
  most preferred term is the most detailed) but now what. 
  We have policy signatures but how do we put it all 
  together? 
- Does the PosetEnsemble need to be a Module or 
  a Module Type? Nothing is going to inherit from 
  PosetEnsemble but we need to be able to reuse it. 
  How do we do that? 
- Do we move onto making a lattice? 

- What about an environment? Do we want that to 
  better specify the system? Maybe that is how the 
  situational awareness is implemented? 

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

Module VirusCheckerEx. 
  (* Simplist example is to ask place 1 to return a hash of its virus checker *)
  Definition req1 := att 1 (asp (HSH)). 

  (* Here are the possible terms (pt) the target sends in the proposal
     pt1 returns the Copland phrase to hash the virus checker
     pt2 asks place 1 to return a signed hash of the virus checker 
     pt3 ensures freshness by introducing a nonce that becomes inital evidence 
         passed to the @1 term where the nonce evidence is sent to CPY and 
         the USM measures a hash of the virus checker *)
  Definition pt1 := att 1 (asp (HSH)).
  Definition pt2 := lseq (att 1 (asp (HSH))) (asp (SIG)).
  Definition pt3 := lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG)).  


  (* The appraiser's privacy policy must allow for the hash request *)
  Inductive A_PP : Plc -> Term -> Prop :=
  | HSH_A_PP : forall (p : Plc) (t : Term), t = att 1 (asp HSH) -> A_PP p t. 

  (* The target selects any terms that match hsh *)
  (* Not entirely certain what t2 should be here, I just want a term that has an ASP in it? 
     Is there an "IN" operation for sets? *)
  Inductive T_SP : Plc -> Term -> Term -> Prop :=
  | HSH1_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) -> t2 = att 1 (asp HSH) -> T_SP p t1 t2 
  | HSH2_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                t2 = lseq (att 1 (asp (HSH))) (asp (SIG)) ->
                                                T_SP p t1 t2
  | HSH3_T_SP : forall (p : Plc) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                t2 = lseq (att 0 (asp (ASPC 0))) (lseq (bpar (ALL, NONE) (asp CPY) (asp HSH)) (asp SIG)) ->
                                                T_SP p t1 t2.

  
  (* The target must ensure all terms satisfy its 
     Privacy Policy before sending the proposal back *)
  Inductive T_PP : Plc -> Term -> Prop :=
  | HSH_T_PP : forall (p : Plc) (t : Term), t = att 1 (asp HSH) -> T_PP p t. 

  (* The appraiser looks at the proposal and selects the "best term"
     Here, best is the one that matches most closely to the request. *)
  (* Let t1 be the request, pr the proposal and t2 be the selected term. *)
  (* Does the appraiser need to take into account the request here? *)
  Inductive A_SP : Plc -> Term -> Proposal -> Term -> Prop :=
  | HSH1_A_SP : forall (pl : Plc) (pr : Proposal) (t1 t2: Term), t1 = att 1 (asp HSH) ->
                                                                 pr = Add _ (Add _ (Singleton _ pt1) pt2) pt3 ->
                                                                 t2 = att 1 (asp HSH) ->
                                                                 A_SP pl t1 pr t2.
  
  
  Definition t_1 : Tpolicy := {|
                                T_privacy := T_PP;
                                T_selection := T_SP
                              |}.

  Definition a_1 : Apolicy := {|
                               A_privacy := A_PP;
                               A_selection := A_SP
                             |}.


  (* 1. What if the proposal is empty? What is the fail case?
        - empty set is the fail case, we just need that case to prove false
     2. What can you prove about this? What kinds of proofs can you do over relations?   
     3. Do I need to write a function? If so, where does that function fit? I am 
     thinking a function that selects the term for attestation based on the policies? 
   *)

  (* Lets introduce a term that would violate the target's privacy policy and prove that 
     that term wouldn't work. *)
  Definition na_1 := (att 1 (asp (ASPC 1))).

  Lemma tar_allows_hsh_vc : T_PP (1) (att 1 (asp HSH)). 
  Proof. 
    apply HSH_T_PP. reflexivity.
  Qed.

  Lemma tar_notallow_cpy : T_PP (1) (att 1 (asp CPY)) -> False. 
  Proof. 
    intros. inversion H. discriminate H0.
  Qed.

  Lemma tar_notallow_cpy' : T_PP (1) (att 1 (asp CPY)).
  Proof. 
    apply HSH_T_PP.
  Abort. 

  (* I think we also need a function that selects the 
     correct term in the proposal. *)




  
End VirusCheckerEx. 
  
  (* This definition uses subset types to say 
     the only term that fits the definition is KIM 3*)
  Definition privacy_sub : {t:term | t = (KIM 3)}. 
  Proof.
    econstructor. reflexivity. 
  Qed.
                                    








