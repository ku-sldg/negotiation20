(* Will not except a measurement of the signautre server *)

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

(* Definition privPolicyTProp p e (t:term e) := privPolicyProp p e. *) 

(* SELECTION FUNCTION *)
Definition selectDep p e (t0:term e) := {t:term e | privPolicyProp p e}.


(* Measure the VC *)
Definition vc := TMeas (EAt VC (EBlob green)).  
Compute selectDep AP _ vc. 
(* = {_ : term (EAt VC (EBlob green)) | True}
     : Set *)
Example vc_okay : selectDep AP _ vc.
Proof. unfold selectDep. exists (TMeas (EAt VC (EBlob green))). unfold privPolicyProp. auto. Qed.

Check proj1_sig (vc_okay).

(* Measure VC and sign the result *)
Definition vc_sign := TMeas (ESig (EAt VC (EBlob green)) TP).
Compute selectDep AP _ vc_sign. 

Example vc_sign_okay : selectDep AP _ vc_sign.
Proof. unfold selectDep. exists (TMeas (ESig (EAt VC (EBlob green)) TP)). unfold privPolicyProp. auto. Qed.

Check proj1_sig (vc_sign_okay).
(*: term (ESig (EAt VC (EBlob green)) TP)*)


(* Measure VC and SS in sequence *)
Definition vc_ss := TMeas (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)).

Compute selectDep AP _ vc_ss. 
(* = {_ : term (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)) | True /\ False}
     : Set*)

(* Proof is left in a `False` state. *)
Example vc_ss_okay : selectDep AP _ vc_ss.
Proof. unfold selectDep. exists (TMeas (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP))).
       unfold privPolicyProp. split. auto. Abort. 

