
Require Import Coq.Lists.List.

(* Will not except a measurement of the signautre server *)
Module subset1. 
Inductive place : Type :=
| VC : place
| SS : place
| OP : place
| t_pub_key : place 
| t_priv_key : place 
| a_pub_key : place.

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

Definition good_encrypt := t_pub_key :: a_pub_key :: nil. 

Fixpoint privPolicy (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | ECrypt e' ep => if (in_dec (eq_place_dec) ep good_encrypt) 
                         then (match e' with 
                                 | EBlob red => True 
                                 | _ => privPolicy e'
                              end) 
                          else privPolicy e'
    | ESig e' p => privPolicy e'
    | ESeq l r => and (privPolicy l) (privPolicy r)
    | EPar l r => and (privPolicy l) (privPolicy r)
    | EAt p e' => match p with 
                  | OP => False 
                  | _ => privPolicy  e' 
                  end
    end.


(* Definition privPolicyTProp p e (t:term e) := privPolicyProp p e. *) 

(* SELECTION FUNCTION *)
Definition selectDep e (_ :term e) := {t:term e | privPolicy e}.


(* Measure the VC *)
Definition vc := TMeas (EAt VC (EBlob green)).  
Compute selectDep _ vc. 
(* = {_ : term (EAt VC (EBlob green)) | True}
     : Set *)
(*Compute proj2_sig (selectDep _ vc).*)

Example vc_okay : selectDep _ vc.
Proof. unfold selectDep.  exists (TMeas (EAt VC (EBlob green))). simpl.  unfold privPolicy. auto. Qed.

Check proj1_sig (vc_okay).
(* : term (EAt VC (EBlob green))*)

Check proj2_sig (vc_okay).

(* Measure VC and sign the result *)
Definition vc_sign := TMeas (ESig (EAt VC (EBlob green)) t_priv_key).
Compute selectDep _ vc_sign. 

Example vc_sign_okay : selectDep _ vc_sign.
Proof. unfold selectDep. exists (TMeas (ESig (EAt VC (EBlob green)) t_priv_key)). unfold privPolicy. auto. Qed.

Check proj1_sig (vc_sign_okay).
(*: term (ESig (EAt VC (EBlob green)) TP)*)


(* Measure VC and SS in sequence *)
Definition vc_ss := TMeas (EPar (ESig (EAt VC (EBlob green)) t_priv_key) (ESig (EAt SS (EBlob green)) t_priv_key)).

Compute selectDep _ vc_ss. 
(* = {_ : term (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)) | True /\ False}
     : Set*)

(* Proof is left in a `False` state. *)
Example vc_ss_okay : selectDep _ vc_ss.
Proof. unfold selectDep. exists (TMeas (EPar (ESig (EAt VC (EBlob green)) t_priv_key) (ESig (EAt SS (EBlob green)) t_priv_key))).
       unfold privPolicy. split. auto. auto. Qed.    

(* Measure VC and OP in sequence *)
Definition vc_op := TMeas (EPar (ESig (EAt VC (EBlob green)) t_priv_key) (ESig (EAt OP (EBlob green)) t_priv_key)).

Compute selectDep _ vc_op. 
(* = {_ : term (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)) | True /\ False}
     : Set*)

(* Proof is left in a `False` state. *)
Example vc_op_okay : selectDep _ vc_op.
Proof. unfold selectDep. 
       exists (TMeas (EPar (ESig (EAt VC (EBlob green)) t_priv_key) (ESig (EAt OP (EBlob green)) t_priv_key))).
       unfold privPolicy. split. auto. Abort. 



End subset1. 

Module Subset2.

Inductive class : Type :=
| VC : class
| SS : class
| OP : class.

Inductive place : Type :=
| target : place
| appraiser : place
| t_pub_key : place 
| t_priv_key : place 
| a_pub_key : place.

Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
Proof.
repeat decide equality.
Defined.



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

Check TMeas (EBlob VC).

Definition good_encrypt := t_pub_key :: a_pub_key :: nil. 

Fixpoint privPolicy (e:evidence): Prop :=
  match e with
  | EHash => True
  | EBlob OP => False
  | EBlob _ => True
  | ECrypt e' ep => if (in_dec (eq_place_dec) ep good_encrypt) 
                    then (match e' with 
                        | EBlob red => True 
                        | _ => privPolicy e'
                        end) 
                    else privPolicy e'
  | ESig e' p => privPolicy e'
  | ESeq l r => and (privPolicy l) (privPolicy r)
  | EPar l r => and (privPolicy l) (privPolicy r)
  | EAt p e' => privPolicy  e'
  end.
  
  
  (* Definition privPolicyTProp p e (t:term e) := privPolicyProp p e. *) 
  
  (* SELECTION FUNCTION *)
  Definition selectDep e (_ :term e) := {t:term e | privPolicy e}.
  
  
  (* Measure the VC *)
  Definition vc := TMeas (EAt target (EBlob VC)).  
  Compute selectDep _ vc. 
  (*= {_ : term (EAt target (EBlob VC)) | True}
  : Set *) 
  
  Example vc_okay : selectDep _ vc.
  Proof. unfold selectDep.  exists (TMeas (EAt target (EBlob VC))).  unfold privPolicy. auto. Qed.
  
  Check proj1_sig (vc_okay).
  (* : term (EAt target (EBlob VC)) *)
  
  Check proj2_sig (vc_okay).
  
  (* Measure VC and sign the result *)
  Definition vc_sign := TMeas (ESig (EAt target (EBlob VC)) t_priv_key).
  Compute selectDep _ vc_sign. 
  
  Example vc_sign_okay : selectDep _ vc_sign.
  Proof. unfold selectDep. exists (TMeas (ESig (EAt target (EBlob VC)) t_priv_key)). unfold privPolicy. auto. Qed.
  
  Check proj1_sig (vc_sign_okay).
  (*: term (ESig (EAt VC (EBlob green)) TP)*)
  
  
  (* Measure VC and SS in sequence *)
  Definition vc_ss := TMeas (EPar (ESig (EAt target (EBlob VC)) t_priv_key) (ESig (EAt target (EBlob SS)) t_priv_key)).
  
  Compute selectDep _ vc_ss. 
  (* = {_ : term (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)) | True /\ False}
  : Set*)
  
  (* Proof is left in a `False` state. *)
  Example vc_ss_okay : selectDep _ vc_ss.
  Proof. unfold selectDep. exists (TMeas (EPar (ESig (EAt target (EBlob VC)) t_priv_key) (ESig (EAt target (EBlob SS)) t_priv_key))).
  unfold privPolicy. split. auto. auto. Qed.    
  
  (* Measure VC and OP in sequence *)
  Definition vc_op := TMeas (ESeq (ESig (EAt target (EBlob OP)) t_priv_key) 
                                  (ESig (EAt target (EBlob VC)) t_priv_key)).
  
  Compute selectDep _ vc_op. 
  (* = {_ : term (EPar (ESig (EAt VC (EBlob green)) TP) (ESig (EAt SS (EBlob green)) TP)) | True /\ False}
  : Set*)
  
  (* Proof is left in a `False` state. *)
  Example vc_op_okay : selectDep _ vc_op.
  Proof. unfold selectDep. 
  exists (TMeas (EPar (ESig (EAt target (EBlob OP)) t_priv_key) 
                      (ESig (EAt target (EBlob VC)) t_priv_key))).
  unfold privPolicy. split. auto. Abort.
  
End Subset2.
  
  
  
  