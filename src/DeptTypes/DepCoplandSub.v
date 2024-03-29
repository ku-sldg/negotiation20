Set Implicit Arguments.

Module DepCopland.

  (* Define three places named [AA], [BB], and [CC] *)
  Inductive place : Type :=
  | AA : place
  | BB : place
  | CC : place.

  (* Define two classification levels.  [red] is classified and [green] is
     unclassified. *)
  Inductive class : Type :=
  | red : class
  | green : class.

  Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
  Proof.
    repeat decide equality.
  Defined.
  
  (* [evidence] type generated by term. The argument [n] allows for multiple
     subtypes.  [EBlob 1] is a different evidenence type than [EBlob 2]. All
     this does is allow more kinds of evidence without extending this type.

     - [EBlob class] - Arbitrary evidence that can be sensitive ([red]) or
       public ([green]).
     - [EHash] - Hash value.  All hash values are [green].
     - [EPrivKey p] - Private Key for place p.  [PubKey p] is
       inverse.  Always [red] and should never be exposed.
     - [EPubKey p] - Public Key for place p. [PrivKey p] is
       inverse. Usually safe?  Will treat as always [green] for this
       experiment.
     - [ESessKey n] - Symmetric session key. [n] allows recording which
       session key in the type.  Will treat as always [red] for this
       experiment.
     - [ECrypt e p] - [e] of type [evidence] encrypted with public
       key of [p].  Always safe and [green].
     - [ESig e p] - [e] signed by [private p].  Safe if [e] is safe, so can be
       either [red] or [green]
     - [ESeq l r] - Sequential composition of evidence [l] and [r].  [green] if
       [l] and [r] are [green].
     - [EPar l r] - Parallel composition of evidence [l] and [r].  [green] if
       [l] and [r] are [green].
     - [EAt p e] - Evidence [e] is gathered from place [p]. This could be 
       red if the place should not be measured.  

     [evidence] is the type corresponding with these definitions.
   *)
  
  Inductive evidence : Type :=
  | EBlob : class -> evidence
  | EHash : evidence
  | EPrivKey : place -> evidence
  | EPubKey : place -> evidence
  | ESessKey : nat -> evidence
  | ECrypt : evidence -> place -> evidence
  | ESig : evidence -> place -> evidence
  | ESeq : evidence -> evidence -> evidence
  | EPar : evidence -> evidence -> evidence
  | EAt : place -> evidence -> evidence. 

  Definition eq_ev_dec: forall x y:evidence, {x=y}+{x<>y}.
  Proof.
    repeat decide equality.
  Defined.

  (* [term] type indexed on evidence produced. Each term type captures the
     type of evidence resulting from execution.

   - [TMeas e] - gather basic evidence value.  Could be any evidence type
   - [THash e] - results in a hash.
   - [TCrypt e p] - results in an encrypted thing using place [p]'s encryption
     key. For session keys [p] can be any aribitrary value.
   - [TSig e p] - results in a signed thing using place [p]'s local signing key.
   - [TSeq e f] - [e] followed by [f]
   - [TPar e f] - [e] in parallel with [f]
   - [TAt p e] - gather evidence [e] from place [p]
   *)
  Inductive term : evidence -> Type :=
  | TMeas : forall e, term e
  | THash : forall e, term e -> term EHash
  | TCrypt : forall e p, term e -> term (ECrypt e p)
  | TSig : forall e p, term e -> term (ESig e p)
  | TSeq : forall e f, term e -> term f -> term (ESeq e f)
  | TPar : forall e f, term e -> term f -> term (EPar e f)
  | TAt : forall e p, term e -> term (EAt p e).
  
  (* | TPlace : forall p e, place p -> term e -> term (EPlace p e).
      This construstor didn't work. Although, I think it is what we 
      would like to say. 
  
  *)

  (* [term e] is indexed on [evidence] in a manner similar to an indexed abstract
     syntax for a programming language.  Every term is accompanied by the evidence
     type it produces.  Following are a few examples:
   *)
  
  Check TMeas (EBlob red).
  Definition blob := TMeas (EBlob red).
  Check (TSeq (TSig AA blob) (TPar blob (TPar blob blob))).
  Check (TSeq (TSig AA blob) (THash (TPar blob (TPar blob blob)))).
  Check THash (TMeas (EBlob red)).
  Check THash (TSig BB (TMeas (EBlob red))).
  Check (TSig BB (TMeas (EBlob red))).
  Check (TSeq (THash (TMeas (EBlob red))) (TMeas EHash)).
  Check TSeq (THash (TMeas (EBlob red))) (TSig AA (TMeas (EBlob red))).
  Check TSeq (THash (TMeas (EBlob red))) (TCrypt AA (TMeas (EBlob red))).
  Check TSeq (THash (TMeas (EPrivKey AA))) (TCrypt AA (TMeas (EBlob red))).
  Check TSeq (TMeas (EPrivKey AA)) (TCrypt AA (TMeas (EBlob red))).
  Check TAt AA (THash (blob)). 

  (* Blobs are things that may or may not need to be protected.  A hash
     typically will not need protection but a private key will.  There
     are various things one can do to blobs - hashing, signing, encrypting
     are the big three.  Hashing and encrypting protect blobs while signing
     does not.  Hashing always protects blobs.  Encrypting protects blobs
     unless the adversary can obtain inverse key to decrypt.

     Assume that some place [AA] has a privacy policy that does not allow any
     blob that is not a hash to be released.  The protocol:

     TSeq (THash (TMeas (EBlob red))) (TMeas EHash)
     : term (ESeq EHash EHash)

     satisfies this because its type tells us it returns a sequence of
     hashes.

     The protocol:

     TSeq (THash (TMeas (EBlob red))) (TSig AA (TMeas (EBlob 0)))
     : term (ESeq EHash (ESig (EBlob red) AA))

     does not satisfy this because its type tells us it returns a
     signature over (EBlob red) that does not protect it.

     In contrast, the protocol:
     
     TSeq (THash (TMeas (EBlob red))) (TCrypt AA (TMeas (EBlob red)))
     : term (ESeq EHash (ECrypt (EBlob red) AA))

     again satisfies this because its type tells us it returns
     an encrypted (EBlob 0) that protects it.

     Now a harder one:

     TSeq (TMeas EPrivKey) (TCrypt AA (TMeas (EBlob red)))
     : term (ESeq EPrivKey (ECrypt (EBlob red) AA))

     Literally we do not meet the requirement of only returning hashes and
     encrypted data.  But how dangerous is this protocol?  There is a private
     key returned by the first term.  Never good, but even worse if that
     private key corresponds with the encrypted blob.  Because we do not
     record whose private key this is we cannot make a strong assessment.
     
     Changing the definition of EPrivKey just a bit allows a stronger
     assessment:

     TSeq (TMeas (EPrivKey AA)) (TCrypt AA (TMeas (EBlob red)))
     : term (ESeq (EPrivKey AA) (ECrypt (EBlob red) AA))

     Here EPrivKey records whose private key is being reported.  Now we know
     this is particularly dangerous.  While this is a rather contrived
     example, remember that we are trying to prevent errors in attestation
     protocols, not prevent adversaries from writing hostile protocols.

   *)

  (* Now if we can express privacy policy over [evidence] in the type space
     we will have privacy checking in the type system.  This is next!!
   *)
  
  (* A function that checks signatures.  Basically, if the signed thing is
     signed by the provided place, the check is true. We've switched to
     the term space here and are not using typing results.
   *)
  Definition checkSig (t:evidence)(p q:place)(e: term (ESig t p)) : Prop :=
    p = q.

  (* A privacy policy that maps each evidence type to [True] or [False] indicating
     whether evidence can be exposed. *)
  
  Fixpoint privPolicy (e:evidence): bool :=
    match e with
    | EHash => true
    | EBlob red => false
    | EBlob green => true
    | EPrivKey _ => false
    | EPubKey _ => true
    | ESessKey _ => false
    | ESig e' _ => privPolicy e'
    | ECrypt _ _ => true
    | ESeq l r => andb (privPolicy l) (privPolicy r)
    | EPar l r => andb (privPolicy l) (privPolicy r)
    | EAt p e' => privPolicy e' 
    end.

    (* 
      Do we need to check that the place is okay to meausre from? 
      For that, I think we would need a whole other data structure 
      saying if the place can be measured or not. 
    *)

  (* Privacy policy defined over [term] rather than [evidence] if such a thing
     is ever needed.
   *)
  
  Definition privPolicyT e (t:term e) := privPolicy e.

  (* This privacy policy is defined over evidence *)
  Definition privPolicySat e := (privPolicy e = true).
  Check privPolicySat.

  Compute privPolicySat (EHash). 
  Compute privPolicySat (EBlob red).
  (* this give us " = false = true " which is an impossible proof *)

  Definition privPolicyTSat e (t:term e) := (privPolicyT t = true).
  Check privPolicyTSat.
  
  (* Some examples that seem to indicate we can extract and use the evidence type.
     Note this is not a typecheck type, but at run time *)

  Compute privPolicyT (TMeas (EBlob red)).
  Compute privPolicyT (THash (TMeas (EBlob red))).
  Compute privPolicyT (TCrypt AA (TMeas (EBlob red))).
  Compute privPolicyT (TSig AA (TMeas (EBlob red))).
  Compute privPolicyT (TSig BB (TCrypt AA (TMeas (EBlob red)))).
  Compute privPolicyT (TAt AA (TMeas (EBlob red))).
  Compute privPolicyT (TAt AA (THash (TMeas (EBlob red)))).

  (* Some helper proofs used as input to the selection function. *)
  Lemma pp0: privPolicy (EBlob green) = true.
  Proof.
    auto.
  Qed.

  Lemma pp1: privPolicy (EBlob red) = true -> False.
  Proof.
    intros.
    simpl in H.
    inversion H.
  Qed.

  Lemma pp2: true = privPolicyT (TMeas (EBlob green)).
  Proof.
    auto.
  Qed.

  Lemma pp3 : forall p : place, privPolicyT (TAt p (THash (TMeas (EBlob red)))) = true.
  Proof. 
    auto. 
  Qed.  

  (* Subset domain type defining all policies that satisfy [privPolicyT].
     Defined the signature for such functions, but not actual example
     functions yet. Coq type checker is stopping me from doing anything
     reasonable.
   *)

  Lemma ex1: privPolicySat (EBlob green).
    unfold privPolicySat.
    auto.
  Qed.
  
  Compute (exist privPolicySat (EBlob green) ex1).

  Lemma ex2: privPolicyTSat (TMeas (EBlob green)).
    unfold privPolicyTSat.
    auto.
  Qed.

  Lemma ex3: privPolicyTSat (THash (TMeas (EBlob red))).
    unfold privPolicyTSat.
    auto.
  Qed.
  
  Compute (exist privPolicySat (EBlob green) ex2).
  
  Compute (exist _ (THash (TMeas (EBlob red))) ex3).

  Definition selectDep''' e (t:term e) : {e:evidence | (privPolicySat e)} :=
    (exist privPolicySat (EBlob green) ex2).

  Fixpoint privPolicyProp (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob red => False
    | EBlob green => True
    | EPrivKey _ => False
    | EPubKey _ => True
    | ESessKey _ => False
    | ESig e' _ => privPolicyProp e'
    | ECrypt _ _ => True
    | ESeq l r => and (privPolicyProp l) (privPolicyProp r)
    | EPar l r => and (privPolicyProp l) (privPolicyProp r)
    | EAt p e' => privPolicyProp e' 
    end.

  Compute privPolicyProp (EBlob red). 

  Definition red_is_False : term (EBlob red) -> False.
  Proof.
    intros. inversion H. Abort.

  (* in CPDT on pg 104 where pred_strong is defined, Chipila has a 
     construstor for every case. *)
     
  (* I would like to say {e : evidence} | privPolicy e : term e := *)   
  (* Definition select_strong e (t : term e): {e : evidence  | privPolicySat e} :=
    match e with 
    | exist (EBlob red) pf => match pp1 pf with end 
    | exist e' _ => e' 
    end. *)


  (* It is the EBlob red where I can't get false = true to prove. Need to look more into how to 
     prove that. *)  
  Definition selectDep'''' e (t : term e) : {e : evidence | (privPolicyProp e)}.
    Proof. exists e. induction e.
    + destruct c.
    ++ simpl. apply pp1. simpl. Abort.
  
  Compute selectDep''' (THash (TMeas (EBlob green))).

End DepCopland.
  (*
    What if we include privacy policy satisfaction proofs in the terms
    themselves?  No proof, no term.
   *)


Module IndexedCopland.

  (* Define three places named [AA], [BB], and [CC] *)
  Inductive place : Type :=
  | AA : place
  | BB : place
  | CC : place.

  (* Define two classification levels.  [red] is classified and [green] is
     unclassified. *)
  Inductive class : Type :=
  | red : class
  | green : class.

  (* Proof that the class is decidable *)
  Definition eq_class_dec: forall x y:class, {x=y}+{x<>y}.
  Proof.
    repeat decide equality.
  Defined.

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

  (*
  Definition eq_ev_dec: forall p, forall x y:evidence p, {x=y}+{x<>y}.
  Proof.
    intros p x y.
    repeat decide equality.
  Defined.
   *)

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

  (* try a lemma with place *)
  Lemma l4: forall p, privPolicy (EAt p (EBlob p green)).
    unfold privPolicy; auto.
  Qed.   

  (* Here we could generalize the lemma to work for all t that satisfy the privacy policy *)
  Lemma l5: forall (p:place) (e:evidence p), privPolicy e = True -> term e.
  Proof.
    induction e; intros; apply TMeas.
  Qed.

  (* Good AST *)
  Compute TMeas (EBlob AA green).
  Compute TMeas (EBlob AA red).
  Compute THash (TMeas (EBlob AA red)) (l3 AA).
  Compute TCrypt (TMeas (EBlob AA red)) (l2 AA AA).
  Compute TSig AA (TMeas (EBlob AA green)) (l1 AA).
  Compute TSeq (TSig BB (TMeas (EBlob BB green)) (l1 BB)) (l1 BB)
               (TCrypt (TMeas (EBlob BB red)) (l2 BB BB)) (l2 BB BB).
  Compute TAt BB (TMeas (EBlob AA green)) (l4 BB).

  (* Bad AST *)
  Compute TSig BB (TMeas (EBlob AA red)).
  Compute THash (TMeas (EPrivKey AA)).

End IndexedCopland. 

  


