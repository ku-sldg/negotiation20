Set Implicit Arguments.
Require Import Ensembles. 

Module IndexedCopland.

    (* The place is where we want the measurement from *)
    Inductive place : Type :=
    | AA : place
    | BB : place
    | CC : place.

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

    (* Evidence structure indexed on the place. 
       This means place is captured with evidence *)
       (* the place here is where we want the measurement to be taken *)
    Inductive evidence : place -> Type :=
    | EBlob : forall p, class -> evidence p
    | EHash : forall p, evidence p
    | ECrypt : forall p q, evidence q -> place -> evidence p
    | ESig : forall p q, evidence q -> place -> evidence p
    | ESeq : forall p q r, evidence p -> evidence q -> evidence r
    | EPar : forall p q r, evidence p -> evidence q -> evidence r.


    Compute (ECrypt AA (EHash AA) AA). 

    (*
    BB = place to do encrypting 
    CC = place blob is encrypted for 
         only CC will be able to decrypt the blob  
    *)
    Compute (ECrypt BB (EBlob AA red) CC).
    (* evidence BB *) 

    Compute (ECrypt CC (EBlob AA red) CC).

    (* The privacy policy is a mapping from evidence to proposition *)
    Fixpoint privPolicy tp (ap:place) (e:evidence tp): Prop :=
        match ap, e with
        | _ , EHash _ => True
        | _ , EBlob _ red => False
        | _ , EBlob _ green => True
        | ap, ESig _ e' _ => privPolicy ap e'
        | ap, ECrypt p e' tp => if eq_place_dec ap tp then privPolicy ap e' else True
        | _ , ESeq _ l r => (privPolicy ap l) /\ (privPolicy ap r)
        | _ , EPar _ l r => (privPolicy ap l) /\ (privPolicy ap r)
        end.

   Compute privPolicy CC (ECrypt BB (EBlob AA red) CC).
   Compute privPolicy AA (ECrypt BB (EBlob AA red) CC). 
        
   Fixpoint privPolicy' tp (ap:place) (e:evidence tp): Prop :=
      match ap, e with
         | _ , EHash _ => True
         | _ , EBlob _ red => False
         | _ , EBlob _ green => True
         | ap, ESig _ e' _ => privPolicy' ap e'
         | ap, ECrypt _ e' tp => match e' with 
                                 | EBlob p red => if eq_place_dec ap tp then False else True 
                                 | _ => privPolicy' ap e'
                                 end   
         | _ , ESeq _ l r => (privPolicy' ap l) /\ (privPolicy' ap r)
         | _ , EPar _ l r => (privPolicy' ap l) /\ (privPolicy' ap r)
      end.

      Compute privPolicy' CC (ECrypt BB (EBlob AA red) CC).
      Compute privPolicy' AA (ECrypt BB (EBlob AA red) CC). 


    (* terms are indexed on the evidence they produce *)
    Inductive term p:(evidence p) -> Type :=
    | TMeas : forall e, term e
    | THash : forall ap e, term e -> privPolicy ap (EHash p) -> term (EHash p)
    | TSig :
         forall ap e q, term e -> privPolicy ap (ESig p e q) -> term (ESig p e q)
    | TCrypt :
        forall ap e q, term e -> privPolicy ap (ECrypt p e q) -> term (ECrypt p e q)
    | TSeq : forall ap e f,
        term e -> privPolicy ap e -> term f -> privPolicy ap f -> term (ESeq p e f)
    | TPar : forall ap e f,
        term e -> privPolicy ap e -> term f -> privPolicy ap f -> term (EPar p e f).

   Compute TMeas (EBlob _ red). 

    Lemma l1: forall ap p, privPolicy ap (EBlob p green). unfold privPolicy; auto. Qed.

    Lemma l2_green: forall ap p q, privPolicy ap (ECrypt q (EBlob p green) p). unfold privPolicy. intros. destruct eq_place_dec. auto. auto. Qed.
    (* this proof should only work with the prerequisite that ap <> p  *)
    Lemma l2_red: forall ap p q, ap <> p -> privPolicy ap (ECrypt q (EBlob p red) p). intros.   
    unfold privPolicy; intros; destruct eq_place_dec; auto. Qed.
       
       (* BB is the appraiser's place. CC is the place the target should encrypt from. *)
    Compute TCrypt BB CC (TMeas (EBlob AA red)). 
       (* : privPolicy BB (ECrypt AA (EBlob AA red) CC) ->
          term (ECrypt AA (EBlob AA red) CC) *)

    Lemma place_neq_AABB : AA <> BB. 
    Proof. unfold not. intros. discriminate.
    Qed.          
   
    Lemma place_neq_AACC : AA <> CC. 
    Proof. unfold not. intros. discriminate.
    Qed.  

    Compute TCrypt AA CC (TMeas (EBlob BB red)) (l2_red BB place_neq_AACC).
    (* term (ECrypt BB (EBlob BB red) CC)*)

   Compute ECrypt BB (EBlob AA red) CC.
   (* evidence BB *)
   Compute TCrypt BB CC (TMeas (EBlob AA red)).
   (* fun x : privPolicy BB (ECrypt AA (EBlob AA red) CC) =>
       TCrypt BB CC (TMeas (EBlob AA red)) x
     : privPolicy BB (ECrypt AA (EBlob AA red) CC) ->
       term (ECrypt AA (EBlob AA red) CC) *) 
   
   

    Lemma l3: forall ap p, privPolicy ap (EHash p). unfold privPolicy; auto. Qed.
    
    (* this lemma is written to include all pieces of evidence *)
    Lemma l5: forall ap (p:place) (e:evidence p), privPolicy ap e = True -> term e. Proof. induction e; intros; apply TMeas. Qed.

    (* to write a term, you pass the TERM and a PROOF that the 
       term satisfies the privacy policy. *)
    Compute TMeas (EBlob AA green).
    Compute TMeas (EBlob AA red).
    Compute TMeas (ECrypt BB (EBlob AA red) CC).
    Compute THash (TMeas (EBlob AA red)).
    Compute THash (TMeas (EBlob AA red)) (l3 BB AA ).



    (* Compute TSig AA AA (TMeas (EBlob AA green)) (l1 AA).
    Compute TSeq (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
                 (TCrypt (TMeas (EBlob BB red)) (l2 BB BB)) (l2 BB BB).
    Compute TPar (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
                 (TCrypt (TMeas (EBlob BB red)) (l2 BB BB)) (l2 BB BB). *)


End IndexedCopland. 

Module IndexedTypesAgain. 

   (* The place is where we want the measurement from *)
   Inductive place : Type :=
   | AA : place
   | BB : place
   | CC : place
   | DD : place 
   | EE : place .

   (* decidablility *)
   Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
   Proof.
   repeat decide equality.
   Defined.

   Inductive info : Type := 
   | private_key : info 
   | session_key : info
   | public_key : info.  

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

   Compute (ESeq AA (EBlob BB green) (EBlob CC red)).
   (* evidence AA *)
   Compute (ECrypt AA (EBlob BB green) CC).
   (* evidence AA *) 

   (* where do I pass the proof argument here? *)
   Lemma eqAA : AA = AA. reflexivity. Qed.  
   Compute eq_place_dec AA AA. 

   Definition a1 : {AA = AA} + {AA <> AA} := left _ eqAA .
   Check a1. 
   
   Lemma less37: 3<7. Proof. auto. Qed.
   Definition v3: {3<7}+{~(3<7)} := left _ less37.
   Check left _ less37. 

    Fixpoint privPolicy (ap:place) tp (e:evidence tp): Prop :=
      match e with
      | EHash _ => True
      | EBlob _ red => False
      | EBlob _ green => True
      | ESig _ e' _ => privPolicy ap e'
      | ECrypt _ e' tp => if eq_place_dec ap tp then privPolicy ap e' else True
      | ESeq _ l r => (privPolicy ap l) /\ (privPolicy ap r)
      | EPar _ l r => (privPolicy ap l) /\ (privPolicy ap r)
      end.

   (* Checking to make sure the privacy policy is written correctly for ECrypt. 
      The appraiser's place should should not match the place where encryption is 
      occuring if the blob is red  *)
   Compute privPolicy CC (ECrypt AA (EBlob AA red) CC).
   Compute privPolicy CC (ECrypt CC (EBlob CC red) AA).
   Compute privPolicy CC (ECrypt AA (EBlob AA red) BB).
   
   (* This measuement type checks but would be impossible to write
      with the way the type system works.
      
      For some reason, I can't figure out how to get the crypt 
      measurement to have place CC. It is always the 
      same place as AA *)
   Compute privPolicy CC (ECrypt CC (EBlob AA red) BB).

    (* Terms are indexed on the evidence they produce. First, they expect some measurement.
       That is the first parameter that comes with `term e`. It may also expect the place that 
       is asking for the measurment, ap.  
       
       -> privPolicy ap (EBlob p c)*)
    Inductive term p : evidence p  -> Type :=
    | TMeas : forall ap e,  privPolicy ap e -> term e
    | THash : forall e, e -> term (EHash p)
    | TSig :
         forall ap e q, term e -> privPolicy ap (ESig p e q) -> term (ESig p e q)
    | TCrypt :
        forall (ap q : place) e , place -> term e -> privPolicy ap (ECrypt p e q) -> term (ECrypt p e q)
    | TSeq : forall ap e f,
        term e -> privPolicy ap e -> term f -> privPolicy ap f -> term (ESeq p e f)
    | TPar : forall ap e f,
        term e -> privPolicy ap e -> term f -> privPolicy ap f -> term (EPar p e f).

   Compute TMeas AA (EBlob AA green).
   Compute TMeas AA (EBlob AA red).
   Compute THash AA (EBlob AA red).  

   Lemma greenblob : forall ap p, privPolicy ap (EBlob p green). unfold privPolicy; auto. Qed.   
   Compute TMeas AA AA green (greenblob AA AA).
   (* term (EBlob AA green)*)

   Compute ECrypt BB (EBlob AA green) CC. 
   Compute TCrypt AA BB DD ((TMeas CC AA green) (greenblob CC AA)). 

   (* BEFORE *)
   (* this returns some funky thing where we must provide a proof that the 
      goal is satisfied. As input, we give it the apprasier's place, AA. The place 
      where we want the encryption to occur, and the measurement.  *)
   (* Compute TCrypt AA BB (TMeas _ (EBlob CC green)) . *)
   (* = fun x : privPolicy AA (ECrypt CC (EBlob CC green) BB) =>
       TCrypt AA BB (TMeas (EBlob CC green)) x
     : privPolicy AA (ECrypt CC (EBlob CC green) BB) ->
       term (ECrypt CC (EBlob CC green) BB) *)

   (* AFTER *)
   Compute TCrypt AA BB DD ((TMeas CC AA green) (greenblob CC AA)). 
   (* = fun x : privPolicy AA (ECrypt CC (EBlob CC green) BB) =>
       TCrypt AA BB DD (TMeas CC AA green (greenblob CC AA)) x
     : privPolicy AA (ECrypt CC (EBlob CC green) BB) ->
       term (ECrypt CC (EBlob CC green) BB)*)

   (* it shouldn't matter if ap = tp... the blob is green
      the privacy policy for crypt must take into consideration 
      - ap -- the appraiser's place 
      - mp -- the measurement place 
      - ep -- the evidence gathered place  *)
   Lemma green_crypted: forall ap mp ep, privPolicy ap (ECrypt mp (EBlob mp green) ep).
   Proof. intros. simpl. destruct eq_place_dec. auto. auto. Qed.
   
   Compute TCrypt AA BB CC ((TMeas CC AA green) (greenblob CC AA)) (green_crypted AA CC BB).
   (*  = TCrypt AA BB CC (TMeas CC AA green (greenblob CC AA))
         (green_crypted AA CC BB)
        : term (ECrypt CC (EBlob CC green) BB) 
       
       This says that the green blob measured at place CC is encrypted with BB. *) 

   (* A red measurement should be okay if the appraiser place is not the same as the 
      encryption place (ep)*)
   Lemma red_crypted: forall ap ep r, ap <> ep -> privPolicy ap (ECrypt r (EBlob r red) ep).
   Proof.  intros. unfold privPolicy. destruct eq_place_dec. auto. auto. Qed.
   
   (* This proof is True. It has type AA <> CC *)
   Lemma neqAACC : AA <> CC. unfold not; intros; discriminate. Qed.  
   Check neqAACC. 

   (* for some reason, all we need is ONE proof. We can reuse this proof no 
      matter the places? *)
   Compute TCrypt AA CC (TMeas (EBlob CC red)) (red_crypted AA neqAACC).
   (* = TCrypt AA CC (TMeas (EBlob CC red)) (red_crypted AA neqAACC)
      : term (ECrypt CC (EBlob CC red) CC)*)
   Compute TCrypt AA BB (TMeas (EBlob CC red)) (red_crypted AA neqAACC).   
   (* = TCrypt AA BB (TMeas (EBlob CC red)) (red_crypted AA neqAACC)
     : term (ECrypt CC (EBlob CC red) BB)*)

End IndexedTypesAgain. 

Module SubCopland.

Inductive place : Type :=
| AA : place
| BB : place
| CC : place.

Fixpoint place_match (p1 p2: place) : Prop :=
   match p1 with 
   | AA => True
   | CC => False 
   | BB => True 
   end. 

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

(* privacy policy mapping from evidence to Proposition 

   we MUST define privacy policy over evidence bc we need to make 
   sure the evidence doesn't evalute to expose sensitive information 

   We include place in the privacy policy to make sure that if a red blob 
   is encrypted, the appraiser cannot decrypt it. *)
Fixpoint privPolicyProp (ap : place) (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | ECrypt e tp =>  if eq_place_dec ap tp then privPolicyProp ap e else True
    | ESig e' _ => privPolicyProp ap e'
    | ESeq l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | EPar l r => and (privPolicyProp ap l) (privPolicyProp ap r)
    | EAt p e' => privPolicyProp ap e' 
    end.

    Compute TMeas (ECrypt (EBlob green) AA).
    Compute privPolicyProp (AA) (ECrypt (EBlob green) AA).
    (* = True
     : Prop *)
    Compute privPolicyProp (AA) (ECrypt (EBlob red) AA).
    (* = False
     : Prop*)
    Compute privPolicyProp (BB) (ECrypt (EBlob green) AA).
    (* = True
     : Prop *)
   Compute privPolicyProp (BB) (ECrypt (EBlob red) AA).
   (* We can encrypt a RED blob as long as the place recieving cannot decrypt it
   
      = True 
      : Prop 
   *)

   (* this privacy policy takes in a place asking *)
   Definition privPolicyTProp p e (t:term e) := privPolicyProp p e.

    (* This is our selection policy which creates a set of terms. 
       It builds the set based on privacy policy satisfaction.   *)
    Definition selectDep p e (_:term e) := {t:term e | privPolicyProp p e}.
    
    (* Definition selectDep e (_:term e) := {t:term e | privPolicyProp e}. *)

    Check selectDep. 
    (* selectDep
       : place -> forall e : evidence, term e -> Set*) 
    (* the return type of selectDep is a SET. *)
    
    
    Compute selectDep AA (TMeas (EBlob green)).
    (* = {_ : term (EBlob green) | True}
    : Set *)
    Check selectDep AA (TMeas (EBlob green)).
    
    Compute selectDep AA (THash (TMeas(EBlob red))). 
    (* 
      = {_ : term EHash | True}
     : Set
    *)

    (* if you give me this thing, it is of that type. 
       This is important because you can't have empty types. 
       Type system cannot be empty! *)
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

End SubCopland.

Module SubCopland'.

Inductive place : Type :=
| AA : place
| BB : place
| CC : place.

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

(* privacy policy mapping from evidence to Proposition *)
(* we MUST define privacy policy over evidence bc we need to make 
   sure the evidence doesn't evalute to expose sensitive information *)
(* We include place in the privacy policy to  *)
Fixpoint privPolicyProp (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | ECrypt e p =>  True
    | ESig e' _ => privPolicyProp e'
    | ESeq l r => and (privPolicyProp  l) (privPolicyProp  r)
    | EPar l r => and (privPolicyProp  l) (privPolicyProp  r)
    | EAt p e' => privPolicyProp  e' 
    end.

    Compute TMeas (ECrypt (EBlob green) AA).
    Compute privPolicyProp (ECrypt (EBlob green) AA).
    (* this is a bad measurement if place AA is the one 
       recieving this result. Then place AA would be able 
       to decrypt and then get the red information *)
    Compute privPolicyProp (ECrypt (EBlob red) AA).
    Compute privPolicyProp (ECrypt (EBlob green) AA).

    Definition privPolicyTProp e (t:term e) := privPolicyProp e.

    (* This is our selection policy which creates a set of terms. 
       It builds the set based on privacy policy satisfaction.   *)
    Definition selectDep e (_:term e) := {t:term e | privPolicyProp e}.

    (* When selectDep is applied to this term it returns type `set` *)
    (* we have the subset type.... next need to make it a dependent pair? *)

    Lemma greengood : privPolicyTProp (TMeas (EBlob green)).
    Proof. simpl. reflexivity. Qed.

    (* Example selectDep1' : selectDep (TMeas (EBlob green)) greengood.*)

    (* Term is impossible to write because evidence is red. *)
    Lemma greenandred : ~ privPolicyTProp (TPar (TMeas (EBlob green)) (TMeas (EBlob red))).
    Proof.
      unfold not. intros.
      unfold privPolicyTProp in H. unfold privPolicyProp in H.  destruct H. exact H0.
    Qed.

    (* check set membership. This doesn't work for now.  *)
    (* Definition is_included : In (selectDep) (TMeas (EBlob green)). *) 
    
    Lemma redfalseP : privPolicyProp ((EBlob red)) -> False.
    Proof.
      unfold privPolicyProp. intros. apply H. 
    Qed.
    
    Definition select_term e (s: {t: (term e) | privPolicyTProp t}) : term e := 
        match s with
        | exist _ (TMeas (EBlob red)) pf => match redfalseP pf with end
        | exist _ t _  => t
        end. 
    
    Eval compute in select_term (exist _ (TMeas (EBlob green)) greengood).

    (* this term will not work. 
    Eval compute in select_term (exist _ (TPar (TMeas (EBlob green)) (TMeas (EBlob red))) greengood).*) 

    Lemma hashred : privPolicyTProp (THash (TMeas (EBlob red))).
    Proof. 
      unfold privPolicyTProp. unfold privPolicyProp. reflexivity.
    Qed. 

    Eval compute in select_term (exist _ (THash (TMeas (EBlob red))) hashred).
 
    (* What should be the relation between these? Right now there is no relation. 
       In Chlipala, he generated the set of all numbers that was once less than 
       the input number in the set. *)
    Definition select_term_all e (s: {t: (term e) | privPolicyTProp t}) : {m: (term e) | privPolicyTProp m} := 
      match s return {m: (term e) | privPolicyTProp m} with
      | exist _ (TMeas (EBlob red)) pf => match redfalseP pf with end
      | exist _ t _  => exist _ t (_)
      end.  
      
End SubCopland'.
        
        
