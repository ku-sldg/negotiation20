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

    Compute TMeas (EBlob AA green).
    Compute TMeas (EBlob AA red).
    Compute THash (TMeas (EBlob AA red)) (l3 AA).
    Compute TCrypt (TMeas (EBlob AA red)) (l2 AA AA).
    Compute TSig AA (TMeas (EBlob AA green)) (l1 AA).
    Compute TSeq (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
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

(* privacy policy mapping from evidence to boolean *)
Fixpoint privPolicy (e:evidence): bool :=
    match e with
    | EHash => true
    | EBlob red => false
    | EBlob green => true
    | ESig e' _ => privPolicy e'
    | ECrypt _ _ => true
    | ESeq l r => andb (privPolicy l) (privPolicy r)
    | EPar l r => andb (privPolicy l) (privPolicy r)
    | EAt p e' => privPolicy e' 
    end.

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

    (*Fixpoint privPolicyProT (e:evidence) (t:term e): Prop :=
      match t with
      | EHash => True
      | EBlob red => False
      | EBlob green => True
      | ECrypt _ _ => True
      | ESig e' _ => privPolicyProp e'
      | ESeq l r => and (privPolicyProp l) (privPolicyProp r)
      | EPar l r => and (privPolicyProp l) (privPolicyProp r)
      | EAt p e' => privPolicyProp e' 
      end.*)

    (* privacy policy defined over terms *)
    Definition privPolicyT e (t:term e) := privPolicy e.

    Definition privPolicyTProp e (t:term e) := privPolicyProp e.

    Lemma redfalse' : False = privPolicyProp ((EBlob red)).
    Proof.
        unfold privPolicyProp. reflexivity.
    Qed.     

    Lemma redfalse : false <> privPolicyT (TMeas (EBlob red)) -> False. 
    Proof.
      intros. 
      unfold privPolicyT in H. unfold privPolicy in H.
      destruct H. reflexivity.
    Qed. 

    Definition selectDep'' e (_:term e) : {t:term e | true = (privPolicyT t)}.
      induction e. destruct c. Abort. 
  
     (* HELP cannot seem to recurse here. Are we going to have to use sumbool??? No sumbool. We aren't comparing things.
          BUT could do a proof that it is in the privPolicy or not in the privPolicy   *)
    Definition selectDep : forall e (t:term e), false <> privPolicyT t -> {t1: term e | privPolicyProp e}.  
    refine (fun t =>
      match t with 
      | EHash => fun _ => exist _ TMeas (EHash) _
      | (EBlob red) => fun pf => match redfalse pf with end
      | (EBlob green) => exist _ TMeas (EBlob green) _
      | ECrypt e' p => exist _ TMeas (ECrypt e' p) _
      | ESig e' _ => privPolicyProp e'
      | ESeq l r => and (privPolicyProp l) (privPolicyProp r)
      | EPar l r => and (privPolicyProp l) (privPolicyProp r)
      | EAt p e' => privPolicyProp e' 
    end). *)
    
    Compute privPolicyT (TMeas (EBlob red)).

    Notation "’Yes’" := (left _ _ _).
    Notation "’No’" := (right _ _ _).
    (*Notation "’Reduce’ x" := (if x then Yes else No) (at level 50).*)

    Definition selectDep'' : forall e (t1:term e),  {t:term e | (privPolicyProp e)}. 
      refine ( fix f (e:evidence) (t:term e) : {t:term e | (privPolicyProp e)} := 
      match t with 
        | TMeas (EHash) => fun _ => exist _ TMeas (EHash) _
        | TMeas (EBlob red) => fun pf => match redfalse pf with end
        | TMeas (EBlob green) => exist _ TMeas (EBlob green) _
        | TMeas (ECrypt e' p) => exist _ TMeas (ECrypt e' p) _
        | TMeas (ESig e' _) => privPolicyProp e'
        | TMeas (ESeq l r) => and (privPolicyProp l) (privPolicyProp r)
        | TMeas (EPar l r) => and (privPolicyProp l) (privPolicyProp r)
        | TMeas (EAt p e') => privPolicyProp e' 
        end).

    Definition select_strong3 e (t:term e) : {t1 : term e | privPolicyProp e}. 
      (exist _ t).


  
    (* selection function that filters the terms that do not 
       satisfy the privacy policy *)
    Definition select_strong e (t: term e) : false <> privPolicyT (TMeas (EBlob red)) -> term e := 
      match t with
      | (TMeas (EBlob red)) => fun pf: (false <> privPolicyT (TMeas (EBlob red))) => match redfalse pf with end
      (*| THash e => fun _ => t
      | TCrypt e p => fun _ => t 
      | TSig e p => fun _ => select_strong e
      | TSeq l r => fun _ => (select_strong l) and (select_strong r)
      | TPar l r => fun _ => (select_strong l) and (select_strong r)
      | TAt p e => fun _ => select_strong e *)
      | _ => fun _ => t
      end.

    Compute select_strong (TMeas (EBlob red)).
    Compute select_strong (TSeq (TMeas (EBlob red)) (TMeas (EBlob green))). 

    (*  privPolicy e <> false *)
    Lemma allredfalse e (t:term e) : false <> privPolicyT t -> False.
    Proof.
        induction e.
        + intros. destruct H. destruct c. 
        ++ simpl. reflexivity.
        ++ simpl. reflexivity. 


    Definition select_strong' e (s: {t: (term e) | false <> privPolicyT (TMeas (EBlob red)) }) : term e := 
        match s with
        | exist (TMeas (EBlob red)) pf => match redfalse pf with end
        | exist _ _  => t
        end. 

    
End SubCopland.
