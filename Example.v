Set Implicit Arguments.

Module Example1.

Inductive place : Type :=
| appraiser : place
| target : place
| ma : place
| q : place.

Inductive class : Type :=
| red : class
| green : class.

Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.

(* evidence as a type *)
Inductive evidence : Type :=
| EBlob : class -> evidence
| EHash : evidence
| ECrypt : evidence -> place -> evidence
| ESig : evidence -> place -> evidence
| ESeq : evidence -> evidence -> evidence
| EPar : evidence -> evidence -> evidence
| EAt : place -> evidence -> evidence.

Definition eq_ev_dec: forall x y:evidence, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.

(* terms indexed based on the evidence they produce *)
Inductive term : evidence -> Type :=
| TMeas : forall e, term e
| THash : forall e, term e -> term EHash
| TCrypt : forall e p, term e -> term (ECrypt e p)
| TSig : forall e p, term e -> term (ESig e p)
| TSeq : forall e f, term e -> term f -> term (ESeq e f)
| TPar : forall e f, term e -> term f -> term (EPar e f)
| TAt : forall e p, term e -> term (EAt p e).

Check TMeas (EBlob green).

(* privacy policy *)

(* Let's say the target does not wish to
   share a measurement from place q 
   with the appraiser *)
Fixpoint privPolicyProp (ap : place) (e:evidence): Prop :=
    match ap, e with
    | _ , EHash => True
    | _ , EBlob red => False
    | _ , EBlob green => True
    | _ , ECrypt e p =>  match ap with 
                           | p => privPolicyProp ap e
                           (* | _ => True *)
                           end
    | _ , ESig e' _ => privPolicyProp ap e'
    | _ , ESeq l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | _ , EPar l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | _ , EAt tp e' => match ap, tp with 
                      | appraiser, q => False 
                      | _ , _ => privPolicyProp ap e' 
                      end
    end.

    Compute TMeas (ECrypt (EBlob green) appraiser).

    (* in this term, the appraiser is asking the target to 
       encrypt a green blob with the target's public key *)
    Compute privPolicyProp (appraiser) (ECrypt (EBlob green) target).
    (* = True
     : Prop *)

     (* the appraiser asks the target to encrypt sensitive information 
        with the appraiser's public key. This is bad! The appraiser 
        could have access to the sensitive information. *)
    Compute privPolicyProp (appraiser) (ECrypt (EBlob red) appraiser).
    (* = False
     : Prop*)

    Definition privPolicyTProp p e (t:term e) := privPolicyProp p e.

    (* This is our selection policy which creates a set of terms. 
       It builds the set based on privacy policy satisfaction.   *)
    Definition selectDep p e (_:term e) := {t:term e | privPolicyProp p e}.

    Check selectDep. 
    (* selectDep
       : forall e : evidence, term e -> Set*) 
    (* the return type of selectDep is a SET. *)
    
    (* The apprasier can ask for a measurement of a green blob*)
    Compute selectDep appraiser (TMeas (EBlob green)).
    (* = {_ : term (EBlob green) | True}
    : Set *)

    (* The appraiser can ask for a hash of a red blob *)
    Compute selectDep appraiser (THash (TMeas (EBlob red))). 
    (* 
      = {_ : term EHash | True}
     : Set *)

    (* The appraiser can ask for a parallel measurement of the green blob and the hash *)
    Compute selectDep appraiser (TPar (TMeas (EBlob green)) (THash (TMeas (EBlob red)))).
    (* 	 = {_ : term (EPar (EBlob green) EHash) | True /\ True}
         : Set *)

    (* the appraiser CANNOT ask for a measurement from place q *)
    Compute selectDep appraiser (TAt q (TMeas (EBlob green))).
    (* 	 = {_ : term (EAt q (EBlob green)) | False}
         : Set *)


    Example selectDep1 : selectDep appraiser (TMeas (EBlob green)).
    Proof. 
      unfold selectDep. exists (TMeas (EBlob green)). reflexivity.
    Qed.

    Check selectDep1.

    Check proj1_sig.
    Check proj1_sig (selectDep1).
    (* proj1_sig selectDep1
	     : term (EBlob green)*)
    Check proj2_sig (selectDep1).
    (* proj2_sig selectDep1
	     : privPolicyProp (EBlob green)*)
    Compute proj1_sig (selectDep1). 
    (* 	 = let (x, _) := selectDep1 in x
         : term (EBlob green)*) 

    (* No way to prove this so you can never get the value of the term. *)
    Example selectDep2: selectDep appraiser (TAt q (TMeas (EBlob green))).
    Proof. unfold selectDep. exists (TAt q (TMeas (EBlob green))). simpl. Abort.  

End Example1.
