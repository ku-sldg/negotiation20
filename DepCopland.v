Set Implicit Arguments.

Module DepCopland.

  (* Define three places named [AA], [BB], and [CC] *)
  Inductive place : Type :=
  | AA : place
  | BB : place
  | CC : place.
  
  (* [evidence] type generated by term. The argument [n] allows for multiple
     subtypes.  [EBlob 1] is a different evidenence type than [EBlob 2]. All
     this does is allow more kinds of evidence without extending this type.

     - [EBlob n] - Arbitrary evidence identified by argument. Unknown safety
       without knowing context.
     - [EHash] - Hash value.  Always safe.
     - [EPrivKey p] - Private Key for place p.  [PubKey p] is
       inverse.  Never safe.
     - [EPubKey p] - Public Key for place p. [PrivKey p] is
       inverse. Usually safe.
     - [ESessKey n] - Symmetric session key. [n] allows recording which
       session key in the type.
     - [ECrypt e p] - [e] of type [evidence] encrypted with public
       key of [p].  Always safe unless private key is available.
     - [ESig e p] - [e] signed by [private p].  Safe if [e] is safe.
     - [ESeq l r] - Sequential composition of evidence [l] and [r].  Safe if
       [l] and [r] are safe.
     - [EPar l r] - Parallel composition of evidence [l] and [r].  Safe if
       [l] and [r] are safe.
   *)
  
  Inductive evidence : Type :=
  | EBlob : nat -> evidence
  | EHash : evidence
  | EPrivKey : place -> evidence
  | EPubKey : place -> evidence
  | ESessKey : nat -> evidence
  | ECrypt : evidence -> place -> evidence
  | ESig : evidence -> place -> evidence
  | ESeq : evidence -> evidence -> evidence
  | EPar : evidence -> evidence -> evidence.

  (* [term] type indexed on evidence produced. Each term type captures the
     type of evidence resulting from execution.

   - [TMeas e] - basic evidence value.  Could be anythning.
   - [THash e] - results in a hash.  Always a hash.
   - [TCrypt e p] - results in an encrypted thing using place p's encryption
     key. For session keys p can be any aribitrary value.
   - [TSig e p] - results in a signed thing using place p's signing key.
     p is always the local signing key.
   - [TSeq e f] - e followed by f
   - [TPar e f] - e in parallel with f
   *)
  Inductive term : evidence -> Type :=
  | TMeas : forall e, term e
  | THash : forall e, term e -> term EHash
  | TCrypt : forall e p, term e -> term (ECrypt e p)
  | TSig : forall e p, term e -> term (ESig e p)
  | TSeq : forall e f, term e -> term f -> term (ESeq e f)
  | TPar : forall e f, term e -> term f -> term (EPar e f).

  (* Each of these types captures the kind of thing evaluting results in. 
     Note that THash obfuscates results by one-way encryption which is
     exactly what we want. *)
  
  Check TMeas (EBlob 0).
  Definition blob := TMeas (EBlob 0).
  Check (TSeq (TSig AA blob) (TPar blob (TPar blob blob))).
  Check (TSeq (TSig AA blob) (THash (TPar blob (TPar blob blob)))).
  Check THash (TMeas (EBlob 0)).
  Check THash (TSig BB (TMeas (EBlob 0))).
  Check (TSig BB (TMeas (EBlob 0))).
  Check (TSeq (THash (TMeas (EBlob 0))) (TMeas EHash)).
  Check TSeq (THash (TMeas (EBlob 0))) (TSig AA (TMeas (EBlob 0))).
  Check TSeq (THash (TMeas (EBlob 0))) (TCrypt AA (TMeas (EBlob 0))).
  Check TSeq (THash (TMeas (EPrivKey AA))) (TCrypt AA (TMeas (EBlob 0))).
  Check TSeq (TMeas (EPrivKey AA)) (TCrypt AA (TMeas (EBlob 0))).

  (* Blobs are things that may or may not need to be protected.  A hash
     typically will not need protection but a private key will.  There
     are various things one can do to blobs - hashing, signing, encrypting
     are the big three.  Hashing and encrypting protect blobs while signing
     does not.  Hashing always protects blobs.  Encrypting protects blobs
     unless the adversary can obtain inverse key to decrypt.

     Assume that some place AA has a privacy policy that does not allow any
     blob that is not a hash to be released.  The protocol:

     TSeq (THash (TMeas (EBlob 0))) (TMeas EHash)
     : term (ESeq EHash EHash)

     satisfies this because its type tells us it returns a sequence of
     hashes.

     The protocol:

     TSeq (THash (TMeas (EBlob 0))) (TSig AA (TMeas (EBlob 0)))
     : term (ESeq EHash (ESig (EBlob 0) AA))

     does not satisfy this because its type tells us it returns a
     signature over (EBlob 0) that does not protect it.

     In contrast, the protocol:
     
     TSeq (THash (TMeas (EBlob 0))) (TCrypt AA (TMeas (EBlob 0)))
     : term (ESeq EHash (ECrypt (EBlob 0) AA))

     again satisfies this because its type tells us it returns
     an encrypted (EBlob 0) that protects it.

     Now a harder one:

     TSeq (TMeas EPrivKey) (TCrypt AA (TMeas (EBlob 0)))
     : term (ESeq EPrivKey (ECrypt (EBlob 0) AA))

     Literally we do not meet the requirement of only returning hashes and
     encrypted data.  But how dangerous is this protocol?  There is a private
     key returned by the first term.  Never good, but even worse if that
     private key corresponds with the encrypted blob.  Because we do not
     record whose private key this is we cannot make a strong assessment.
     
     Changing the definition of EPrivKey just a bit allows a stronger
     assessment:

     TSeq (TMeas (EPrivKey AA)) (TCrypt AA (TMeas (EBlob 0)))
     : term (ESeq (EPrivKey AA) (ECrypt (EBlob 0) AA))

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
     the term space here and are not using typing results. *)
  Definition checkSig (t:evidence)(p q:place)(e: term (ESig t p)) : Prop :=
    p = q.

  (* This will not typecheck.  Trying to check the signature of a thing
     that is not signed. Note this is caught in _typechecking_
  
  Example e0: checkSig 1 (THash 0 (TMeas (EBlob 0))).

  Error:
  The term "THash 0 (TMeas (EBlob 0))" has type "term (EHash 0)"
  while it is expected to have type "term (ESig ?t ?p)".
  *)

  Example e1: checkSig AA (TSig AA (TMeas (EBlob 0))).
  Proof.
    unfold checkSig.
    congruence.
  Qed.
    
  Example e2: checkSig BB (TSig AA (TMeas (EBlob 0))) -> False.
  Proof.
    unfold checkSig.
    intros.
    inversion H.
  Qed.
  
  Fixpoint privPolicy (e:evidence): Prop :=
    match e with
    | EHash => True
    | EBlob _ => False
    | EPrivKey _ => False
    | EPubKey _ => True
    | ESessKey _ => False
    | ESig e' _ => privPolicy e'
    | ECrypt _ _ => True
    | ESeq l r => privPolicy l /\ privPolicy r
    | EPar l r => privPolicy l /\ privPolicy r
    end.
                                   
  Definition selectDep e (t:term e):term e:=
    match t as q in (term e) return (match e with
                                | EHash => term e
                                | EBlob n => term e
                                | EPrivKey _ => term e
                                | EPubKey _ => term e
                                | ESessKey _ => term e
                                | ESig _ _ => term e
                                | ECrypt _ _ => term e
                                | ESeq l r => term e
                                | EPar l r => term e
                                end) with
    | THash _ => THash
    | TMeas e => TMeas (EBlob 0)
    end.
  
End DepCopland.
