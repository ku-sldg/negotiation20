Inductive place : Type :=
| AP : place
| TP : place
| VC : place
| SS : place.

Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.

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
| TSig : forall e p, term e -> term (ESig e p)
| TCrypt : forall e p, term e -> term (ECrypt e p)
| TSeq : forall e f, term e -> term f -> term (ESeq e f)
| TPar : forall e f, term e -> term f -> term (EPar e f)
| TAt : forall e p, term e -> term (EAt p e).

Check TMeas (EBlob green).


Fixpoint privPolicyProp (ap : place) (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | ECrypt e tp =>  if eq_place_dec ap tp then privPolicyProp ap e else True
    | ESig e' _ => privPolicyProp ap e'
    | ESeq l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | EPar l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | EAt p e' => match p with 
                  | SS => False 
                  | _ => privPolicyProp p e' 
                  end
    end.


(* Measure the VC *)
Definition vc := (EAt VC (EBlob green)).  

   (* Measure VC and sign the result *)
Definition vc_sign := ESig (EAt VC (EBlob green)) TP.
   
   (* Measure VC and SS in sequence *)
Definition vc_ss := EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP).

Definition privPolicyTProp p e (t:term e) := privPolicyProp p e.

Definition selectDep p e (t0:term e) := {t:term e | privPolicyTProp p _ t0}.

Compute selectDep AP vc. 
(* = {_ : term (EAt VC (EBlob green)) | True}
     : Set *)
Compute selectDep AP vc_sign. 
Compute selectDep AP vc_ss _. 

Lemma vc_okay : privPolicyTProp AP _ (TMeas (EAt VC (EBlob green))).
Proof. unfold privPolicyTProp. unfold privPolicyProp. auto. Qed.

Compute selectDep AP vc _ vc_okay.

    



Example selectDep1 : selectDep AA (TMeas (EBlob green)).
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

