Set Implicit Arguments.
Require Import Coq.Lists.List.
 
 (* 3 measurements 
   1. VC
   2. sign VC 
   3. VC and SS in parallel *)
 
 (* The place is where we want the measurement from *)
 Inductive place : Type :=
 | AP : place
 | TP : place
 | VC : place
 | SS : place
 | priv_key : place.

 (* decidablility *)
 Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
 Proof.
 repeat decide equality.
 Defined.
 
  (* The class is if the information is sensitive. Red means sensitive *)
 Inductive class : Type :=
 | red : class
 | green : class.

  (* decidablility *)
  Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
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

 Definition good_encrypt := AP :: TP :: nil.

 Fixpoint privPolicy tp (e:evidence tp): Prop :=
   match e with
   | EHash _ => True
   | EBlob p c => match p with 
                  | SS => False 
                  | _ => True 
                  end
   | ESig _ e' _ => privPolicy e' 
   | ECrypt rp e' tp => if (in_dec (eq_place_dec) tp good_encrypt) then (match e' with 
                                                                  | EBlob priv_key red => False 
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
 Compute privPolicy (EBlob priv_key red). 
 Compute privPolicy (ECrypt TP (EBlob priv_key red) AP).


  (* Terms are indexed on the evidence they produce. First, they expect some measurement.
     That is the first parameter that comes with `term e`. It may also expect the place that 
     is asking for the measurment, ap.  
     
     -> privPolicy ap (EBlob p c)*)
  Inductive term p : evidence p  -> Type :=
  | TMeas : forall e,  privPolicy e -> term e
  | THash : forall e, e -> term (EHash p)
  | TSig :
       forall e q, term e -> privPolicy (ESig p e q) -> term (ESig p e q)
  | TCrypt :
      forall (q : place) e , place -> term e -> privPolicy (ECrypt p e q) -> term (ECrypt p e q)
  | TSeq : forall e f,
      term e -> privPolicy e -> term f -> privPolicy f -> term (ESeq p e f)
  | TPar : forall e f,
      term e -> privPolicy e -> term f -> privPolicy f -> term (EPar p e f).

   Lemma vc_green : privPolicy (EBlob VC green).
   Proof. unfold privPolicy. auto. Qed.

   Definition vc := TMeas (EBlob VC green).
   Check vc. (* : privPolicy (EBlob VC green) -> term (EBlob VC green) *)
   Definition vc' := TMeas (EBlob VC green) vc_green.
   Check vc'. (*: term (EBlob VC green) *)

   Definition vc_sig := TSig TP (TMeas (EBlob VC green) vc_green).
   
   Definition vc_ss := False.  (*this will be impossible to write... no proof that EBlob SS satisfies priv policy *)
   

