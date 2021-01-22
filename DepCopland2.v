Set Implicit Arguments.

Module IndexedCopland.

    (* The place is where we want the measurement from *)
    Inductive place : Type :=
    | AA : place
    | BB : place
    | CC : place.

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
    Inductive evidence : place -> Type :=
    | EBlob : forall p, class -> evidence p
    | EHash : forall p, evidence p
    | EPrivKey : forall p, evidence p
    | EPubKey : forall p, evidence p
    | ESessKey : forall p, nat -> evidence p
    | ECrypt : forall p q, evidence q -> place -> evidence p
    | ESig : forall p q, evidence q -> place -> evidence p
    | ESeq : forall p q r, evidence p -> evidence q -> evidence r
    | EPar : forall p q r, evidence p -> evidence q -> evidence r
    | EAt : forall q, place -> evidence q -> evidence q.

    (* The privacy policy is a mapping from evidence to proposition *)
    Fixpoint privPolicy p (e:evidence p): Prop :=
        match e with
        | EHash _ => True
        | EBlob _ red => False
        | EBlob _ green => True
        | EPrivKey _ => False
        | EPubKey _ => True
        | ESessKey _ _ => False
        | ESig _ e' _ => privPolicy e'
        | ECrypt _ _ _ => True
        | ESeq _ l r => (privPolicy l) /\ (privPolicy r)
        | EPar _ l r => (privPolicy l) /\ (privPolicy r)
        | EAt _ e' => privPolicy e'
        end.    

    (* terms are indexed on the evidence they produce *)
    Inductive term p : (evidence p) -> Type :=
    | TMeas : forall e, term e
    | THash : forall e, term e -> privPolicy (EHash p) -> term (EHash p)
    | TCrypt :
        forall e q, term e -> privPolicy (ECrypt p e q) -> term (ECrypt p e q)
    | TSig :
        forall e q, term e -> privPolicy (ESig p e q) -> term (ESig p e q)
    | TSeq : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (ESeq p e f)
    | TPar : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (EPar p e f)
    | TAt : forall p' e, 
        term e -> privPolicy e -> term (EAt p' e).

    Lemma l1: forall p, privPolicy (EBlob p green). unfold privPolicy; auto. Qed.
    Lemma l2: forall p q, privPolicy (ECrypt q (EBlob p red) p). unfold privPolicy; auto. Qed.
    Lemma l3: forall p, privPolicy (EHash p). unfold privPolicy; auto. Qed.
    Lemma l4: forall p, privPolicy (EAt p (EBlob p green)). unfold privPolicy; auto. Qed. 
    
    (* this lemma is written to include all pieces of evidence *)
    Lemma l5: forall (p:place) (e:evidence p), privPolicy e = True -> term e. Proof. induction e; intros; apply TMeas. Qed.

    (* to write a term, you pass the TERM and a PROOF that the 
       term satisfies the privacy policy. *)
    Compute TMeas (EBlob AA green).
    Compute TMeas (EBlob AA red).
    Compute THash (TMeas (EBlob AA red)). 

    (* something about l5 doesn't work right *)
    (* Compute THash (TMeas (EBlob AA red)) (l5 (EHash AA) AA ). *)
    Compute THash (TMeas (EBlob AA red)) (l3 AA ).
    Compute TCrypt (TMeas (EBlob AA red)) (l2 AA AA).
    Compute TSig AA (TMeas (EBlob AA green)) (l1 AA).
    Compute TSeq (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
                 (TCrypt (TMeas (EBlob BB red)) (l2 BB BB)) (l2 BB BB).
    Compute TPar (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
                 (TCrypt (TMeas (EBlob BB red)) (l2 BB BB)) (l2 BB BB).
    Compute TAt BB (TMeas (EBlob AA green)) (l4 BB).

End IndexedCopland. 

Module SubCopland.

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
Fixpoint privPolicyProp (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | ECrypt _ _ => True
    | ESig e' _ => privPolicyProp e'
    | ESeq l r => and (privPolicyProp l) (privPolicyProp r)
    | EPar l r => and (privPolicyProp l) (privPolicyProp r)
    | EAt p e' => privPolicyProp e' 
    end.

    Definition privPolicyTProp e (t:term e) := privPolicyProp e.

    Definition selectDep e (_:term e) := {t:term e | privPolicyProp e}.

    Compute selectDep (TMeas (EBlob green)).
    Compute selectDep (TMeas (EBlob red)).
    Compute selectDep (TPar (TMeas (EBlob green)) (TMeas (EBlob red))).

    Lemma greengood : privPolicyTProp (TMeas (EBlob green)).
    Proof. simpl. reflexivity. Qed.  

    Lemma greenandred : privPolicyTProp (TPar (TMeas (EBlob green)) (TMeas (EBlob red))).
    Proof.
      unfold privPolicyTProp. unfold privPolicyProp. split. reflexivity. Abort.   


    (* tried... but this doesn't work lol *)
    (*Eval compute in selectDep (exist _ (TMeas (EBlob green)) greengood).*)
    
    (* not really sure what this gets us except that with the : we need 
       a proof and with the := we are just set to go. *)
    Example selectDep1 : selectDep (TMeas (EBlob green)).
    Proof. 
      unfold selectDep. exists (TMeas (EBlob green)). reflexivity.
    Qed.
    
    Check selectDep1.
    
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


    Definition select_term_all e (s: {t: (term e) | privPolicyTProp t}) : {m: (term e) | privPolicyTProp m} := 
      match s return {m: (term e) | privPolicyTProp m} with
      | exist _ (TMeas (EBlob red)) pf => match redfalseP pf with end
      | exist _ t _  => t
      end.
    
End SubCopland.
