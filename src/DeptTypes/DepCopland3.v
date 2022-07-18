Set Implicit Arguments.
Require Import Ensembles. 
Require Import Coq.Lists.List.

Definition  my_list := 2::3::nil.

Module IndexedCopland.

   (* The place is where we want the measurement from *)
   Inductive place : Type :=
   | AA : place
   | BB : place
   | CC : place
   | priv_key : place 
   | EE : place.

   (* decidablility *)
   Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
   Proof.
   repeat decide equality.
   Defined.

   Inductive key : Type := 
   | private_key : key 
   | session_key : key
   | public_key : key.  

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
   (* | EKeys : forall p, key -> evidence p *)
   | ECrypt : forall p q, evidence q -> place -> evidence p
   | ESig : forall p q, evidence q -> place -> evidence p
   | ESeq : forall p q r, evidence p -> evidence q -> evidence r
   | EPar : forall p q r, evidence p -> evidence q -> evidence r.

   Compute (ECrypt AA (EBlob AA green) AA). 

   Compute (ESeq AA (EBlob BB green) (EBlob CC red)).
   (* evidence AA *)
   Compute (ECrypt AA (EBlob BB green) AA).
   (* evidence AA *) 

   (* where do I pass the proof argument here? *)
   Lemma eqAA : AA = AA. reflexivity. Qed.  
   Compute eq_place_dec AA AA. 

   Definition a1 : {AA = AA} + {AA <> AA} := left _ eqAA .
   Check a1. 
   
   (* this defines the places that we can encrypt from *)
   Definition good_encrypt := AA :: BB :: nil.

   (* SearchAbout list.*) 

   (* privacy policy mapped over evidence *)
   Fixpoint privPolicy tp (e:evidence tp): Prop :=
   match e with
   | EHash _ => True
   | EBlob _ red => False
   | EBlob _ green => True
   | ESig _ e' _ => privPolicy e'
   | ECrypt rp e' ep => if (in_dec (eq_place_dec) ep good_encrypt) 
                        then (match e' with 
                              | EBlob _  red => True 
                              | _ => privPolicy e'
                           end) 
                        else privPolicy e'
   | ESeq _ l r => (privPolicy l) /\ (privPolicy r)
   | EPar _ l r => (privPolicy l) /\ (privPolicy r)
   end.


   (* Checking to make sure the privacy policy is written correctly for ECrypt. 
      The place for encryption is allow if the place is in good_encrypt  *)
   Compute privPolicy (ECrypt AA (EBlob AA red) CC).
   Compute privPolicy (ECrypt CC (EBlob CC red) AA).
   Compute privPolicy (ECrypt CC (EBlob CC green) AA).
   Compute privPolicy (ECrypt CC (EBlob priv_key red) AA).

   Compute privPolicy (ECrypt AA (EBlob priv_key red) CC).
   
    (* Terms are indexed on the evidence they produce. First, they expect some measurement.
       That is the first parameter that comes with `term e`. It may also expect the place that 
       is asking for the measurment, ap.  
       
       -> privPolicy ap (EBlob p c)*)

   (* This structure means we can't even encrypt anything red... that is information that should not be shared*)
    Inductive term p : evidence p  -> Type :=
    | TMeas : forall c,  privPolicy (EBlob p c) -> term (EBlob p c)
    | THash : term (EHash p)
    | TSig : forall e q, term e -> privPolicy (ESig p e q) -> term (ESig p e q)
    | TCrypt :
        forall e q, term e -> privPolicy (ECrypt p e q) -> term (ECrypt p e q)
    | TSeq : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (ESeq p e f)
    | TPar : forall e f,
        term e -> privPolicy e -> term f -> privPolicy f -> term (EPar p e f).

   Compute TMeas AA green.
   (*  = fun x : privPolicy (EBlob AA green) => TMeas AA green x
     : privPolicy (EBlob AA green) -> term (EBlob AA green)*)

     
   (* should hash only take in a place?? Doesnt really need a blob? *)
   Compute THash (AA).  
   
   Lemma greenblob : forall p, privPolicy (EBlob p green). unfold privPolicy. auto. Qed.   
   Compute TCrypt AA ((TMeas AA red) _) .
   Compute TCrypt AA ((TMeas BB red) _) .
   Compute TMeas AA green (greenblob AA).
   (* term (EBlob AA green)*)

   Compute ECrypt BB (EBlob AA green) CC. 
   (* we want to encryp it for AA *)
   Compute TCrypt AA ((TMeas CC green) (greenblob CC)).
   Compute TCrypt AA ((TMeas CC red) _).
   (* = fun x : privPolicy (ECrypt CC (EBlob CC red) AA) =>
       TCrypt AA (TMeas CC red ?p) x
     : privPolicy (ECrypt CC (EBlob CC red) AA) ->
       term (ECrypt CC (EBlob CC red) AA) *)
   

   Lemma AA_good : In AA good_encrypt.
   Proof. (* SearchAbout In.*) unfold good_encrypt. simpl. left. reflexivity. Qed.

   Lemma red_crypted: In AA good_encrypt -> privPolicy (ECrypt BB (EBlob BB red) AA).
   Proof. intros. simpl. auto. Qed.

   Compute TCrypt AA ((TMeas CC red) _) (red_crypted AA_good).
   (* 	 = TCrypt AA (TMeas CC red ?p) (green_crypted AA_good)
     : term (ECrypt CC (EBlob CC red) AA) *)

End IndexedCopland. 

Export IndexedCopland.

Module SubCopland.

(* place where measurement occurs *)
Inductive place : Type :=
| AA : place
| BB : place
| CC : place.

(* decidability *)
Definition eq_place_dec: forall x y:place, {x=y}+{x<>y}.
Proof.
  repeat decide equality.
Defined.

(* if something is sensitive or not *)
Inductive class : Type :=
| red : class
| green : class.

(* decidablility *)
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
Compute TCrypt AA (TMeas (EBlob green)). 

(* privacy policy mapping from evidence to Proposition 

   we MUST define privacy policy over evidence bc we need to make 
   sure the evidence doesn't evalute to expose sensitive information 

   We include place in the privacy policy to make sure that if a red blob 
   is encrypted, the appraiser cannot decrypt it. *)

Definition good_encrypt := AA :: BB :: nil. 

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
    | ESig e' _ => privPolicy e'
    | ESeq l r => and (privPolicy l) (privPolicy r)
    | EPar l r => and (privPolicy l) (privPolicy r)
    | EAt p e' => privPolicy e' 
    end.

   Compute TMeas (ECrypt (EBlob green) AA).
   Compute privPolicy (ECrypt (EBlob green) AA).
   (* = True
   : Prop *)
   Compute privPolicy (ECrypt (EBlob red) AA).
   (* = False
   : Prop*)
   Compute privPolicy (ECrypt (EBlob green) CC).
   (* = True
   : Prop *)
   Compute privPolicy (ECrypt (EBlob red) CC).
   (* We can encrypt a RED blob as long as the place recieving cannot decrypt it
   = True 
   : Prop 
   *)

   (* this privacy policy takes in a place asking *)
   Definition privPolicyT e (t:term e) := privPolicy e.

   (* This is our selection policy which creates a set of terms. 
      It builds the set based on privacy policy satisfaction.   *)
   Definition selectDep e (_:term e) := {t:term e | privPolicy e}.

   (* Definition selectDep e (_:term e) := {t:term e | privPolicyProp e}. *)

   Check selectDep. 
   (* selectDep
      : forall e : evidence, term e -> Set*) 
   (* the return type of selectDep is a SET. *)



   Compute selectDep  (TMeas (EBlob green)).
   (* = {_ : term (EBlob green) | True}
   : Set *)

   Compute selectDep (THash (TMeas(EBlob red))). 
   (* 
      = {_ : term EHash | True}
      : Set
      *)

    (* if you give me this thing, it is of that type. 
       This is important because you can't have empty types. 
       Type system cannot be empty! *)
    Example selectDep1 : selectDep  (TMeas (EBlob green)).
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

        
        
