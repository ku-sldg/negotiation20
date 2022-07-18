Set Implicit Arguments.
Require Import Coq.Lists.List.
 
Module firsttry. 
(* The class is if the information is sensitive. Red means sensitive *)
Inductive class : Type :=
| red : class
| green : class.

(* decidablility *)
Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
Proof.
repeat decide equality.
Defined.
 (* 3 measurements 
   1. VC
   2. sign VC 
   3. VC and SS in parallel *)
 
 (* The place is where we want the measurement from *)
 Inductive place : Type :=
 | VC : place
 | SS : place
 | OP : place
 | t_pub_key : place 
 | t_priv_key : place 
 | a_pub_key : place.

 (* decidablility *)
 Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
 Proof.
 repeat decide equality.
 Defined.
 

 (* here, the structure of evidence is a Set 
     https://ku-sldg.github.io/copland/resources/coplandcoq/html/Copland.Term.html *)
 (* This structure has type: evidence _ where _ is the place where evidnece is gathered*)
 Inductive evidence : place -> Type :=
 | EBlob : forall p, class -> evidence p
 | EHash : forall p, evidence p
 | ECrypt : forall p q, evidence q -> place -> evidence p
 | ESig : forall p q, evidence q -> place -> evidence p
 | ESeq : forall p q r, evidence p -> evidence q -> evidence r
 | EPar : forall p q r, evidence p -> evidence q -> evidence r.

 Definition good_encrypt := a_pub_key :: t_pub_key :: nil.

 Fixpoint privPolicy tp (e:evidence tp): Prop :=
   match e with
   | EHash _ => True
   | EBlob p c => match p, c with 
                  | OP, red => False 
                  | OP, green => False 
                  | _ , red => False
                  | _ , green => True 
                  end
   | ESig _ e' _ => privPolicy e' 
   | ECrypt rp e' tp => if (in_dec (eq_place_dec) tp good_encrypt) 
                        then (match e' with 
                                | EBlob t_priv_key red => False 
                                | EBlob _ red => True 
                                | _ => privPolicy e'
                              end) 
                        else privPolicy e'
   | ESeq _ l r => (privPolicy l) /\ (privPolicy r)
   | EPar _ l r => (privPolicy l) /\ (privPolicy r)
   end.

   Compute privPolicy (EBlob VC red).
   Compute privPolicy (EBlob SS red).

 (* Checking to make sure the privacy policy is written correctly for ECrypt. 
    The appraiser's place should should not match the place where encryption is 
    occuring if the blob is red  *)
 Compute privPolicy (EBlob t_priv_key red). 
 Compute privPolicy (ECrypt t_priv_key (EBlob t_priv_key red) a_pub_key).


  (* Terms are indexed on the evidence they produce. First, they expect some measurement.
     That is the first parameter that comes with `term e`. It may also expect the place that 
     is asking for the measurment, ap.  
     
     -> privPolicy ap (EBlob p c)*)
    Inductive term p : evidence p  -> Type :=
    | TMeas : forall c,  privPolicy (EBlob p c) -> term (EBlob p c)
    | THash : term (EHash p)
    | TSig :
         forall e q, term e -> privPolicy (ESig p e q) -> term (ESig p e q)
    | TCrypt :
        forall e q, term e -> privPolicy (ECrypt p e q) -> term (ECrypt p e q)
    | TSeq : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (ESeq p e f)
    | TPar : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (EPar p e f).

   Lemma vc_green : privPolicy (EBlob VC green).
   Proof. unfold privPolicy. auto. Qed.

   Definition vc := TMeas VC green.
   Check vc. (* : privPolicy (EBlob VC green) -> term (EBlob VC green) *)
   Definition vc' := TMeas VC green vc_green.
   Check vc'. (*: term (EBlob VC green) *)

    Lemma vc_sig : privPolicy (ESig VC (EBlob VC green) t_priv_key).
    Proof. unfold privPolicy. auto. Qed.  
   
    Definition vc_sig_okay := TSig t_priv_key (TMeas VC green vc_green) vc_sig.
    Check vc_sig. 

    Definition t1 := TSig t_priv_key (TMeas VC green vc_green).
    
  
  End firsttry. 

Module secondtry. 
(* The class is if the information is sensitive. Red means sensitive *)
Inductive class : Type :=
| VC : class
| SS : class
| OP : class.

(* decidablility *)
Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
Proof.
repeat decide equality.
Defined.
 (* 3 measurements 
   1. VC
   2. sign VC 
   3. VC and SS in parallel *)
 
 (* The place is where we want the measurement from *)
 Inductive place : Type :=
 | target : place
 | appraiser : place
 | t_pub_key : place 
 | t_priv_key : place 
 | a_pub_key : place.

 (* decidablility *)
 Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
 Proof.
 repeat decide equality.
 Defined.
 

 (* here, the structure of evidence is a Set 
     https://ku-sldg.github.io/copland/resources/coplandcoq/html/Copland.Term.html *)
 (* This structure has type: evidence _ where _ is the place where evidnece is gathered*)
 Inductive evidence : place -> Type :=
 | EBlob : forall p, class -> evidence p
 | EHash : forall p, evidence p
 | ECrypt : forall p q, evidence q -> place -> evidence p
 | ESig : forall p q, evidence q -> place -> evidence p
 | ESeq : forall p q r, evidence p -> evidence q -> evidence r
 | EPar : forall p q r, evidence p -> evidence q -> evidence r.

 Definition good_encrypt := a_pub_key :: t_pub_key :: nil.

 Fixpoint privPolicy tp (e:evidence tp): Prop :=
   match e with
   | EHash _ => True
   | EBlob p c => match c with 
                  | OP => False 
                  | _  => True 
                  end
   | ESig _ e' _ => privPolicy e' 
   | ECrypt rp e' tp => if (in_dec (eq_place_dec) tp good_encrypt) 
                        then (match e' with 
                                | EBlob t_priv_key red => False 
                                | EBlob _ red => True 
                                | _ => privPolicy e'
                              end) 
                        else privPolicy e'
   | ESeq _ l r => (privPolicy l) /\ (privPolicy r)
   | EPar _ l r => (privPolicy l) /\ (privPolicy r)
   end.

   Compute privPolicy (EBlob target VC).
   Compute privPolicy (EBlob target SS).


  (* Terms are indexed on the evidence they produce. First, they expect some measurement.
     That is the first parameter that comes with `term e`. It may also expect the place that 
     is asking for the measurment, ap.  
     
     -> privPolicy ap (EBlob p c)*)
    Inductive term p : evidence p  -> Type :=
    | TMeas : forall c,  privPolicy (EBlob p c) -> term (EBlob p c)
    | THash : term (EHash p)
    | TSig :
         forall e q, term e -> privPolicy (ESig p e q) -> term (ESig p e q)
    | TCrypt :
        forall e q, term e -> privPolicy (ECrypt p e q) -> term (ECrypt p e q)
    | TSeq : forall e f,
        term e ->  privPolicy e -> term f -> privPolicy f -> term (ESeq p e f)
    | TPar : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (EPar p e f).

    Inductive term2 p : evidence p  -> Type :=
    | TMeas2 : forall c,  privPolicy (EBlob p c) -> term2 (EBlob p c)
    | THash2 : term2 (EHash p)
    | TSig2 :
         forall e q, term2 e -> privPolicy (ESig p e q) -> term2 (ESig p e q)
    | TCrypt2 :
        forall e q, term2 e -> privPolicy (ECrypt p e q) -> term2 (ECrypt p e q)
    | TSeq2 : forall e f,
        term2 e -> term2 f -> term2 (ESeq p e f)
    | TPar2 : forall e f,
        term2 e -> term2 f ->  term2 (EPar p e f).

    Theorem  same_ev : forall p (e: evidence p), term2 e -> term e .
    Proof.
      induction e. 
      + intros. apply TMeas. inversion H. apply H1.
      + intros. apply THash. 
      + intros. Abort.
    

    Lemma vc_proof : privPolicy (EBlob target VC).
    Proof. unfold privPolicy. auto. Qed.

    Definition vc := TMeas target VC.
    Check vc. (* : privPolicy (EBlob VC green) -> term (EBlob VC green) *)
    Definition vc_okay := TMeas target VC vc_proof.
    Check vc. (*: term (EBlob VC green) *)

    Definition vc_sig := ESig target (EBlob target VC) t_priv_key.

    Lemma vc_sig_proof : privPolicy (ESig target (EBlob target VC) t_priv_key).
    Proof. unfold privPolicy. auto. Qed.  

    Definition vc_sig_okay := TSig t_priv_key (TMeas target VC vc_proof) vc_sig_proof.
    Check vc_sig_okay.
    (* term (ESig target (EBlob target VC) t_priv_key) *) 

    Lemma ss_proof : privPolicy (EBlob target SS).
    Proof. unfold privPolicy. auto. Qed.

    Definition ss_sig := ESig target (EBlob target SS) t_priv_key.

    Lemma ss_sig_proof : privPolicy (ESig target (EBlob target SS) t_priv_key).
    Proof. unfold privPolicy. auto. Qed.  
      
    Definition ss_sig_okay := TSig t_priv_key (TMeas target SS vc_proof) ss_sig_proof.
    Check ss_sig_okay.
    
    Definition vc_ss_par := TPar (ss_sig_okay) (ss_sig_proof) (vc_sig_okay) (vc_sig_proof).
    Check vc_ss_par. 

    Lemma op_proof : privPolicy (EBlob target OP).
    Proof. unfold privPolicy. Abort.   

    Definition ss_sig_okay := TSig t_priv_key (TMeas target OP vc_proof) ss_sig_proof.
  
  End firsttry. 