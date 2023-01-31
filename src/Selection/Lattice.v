(* Lattice is an algebric structure with a Meet and Join 
   
   If we make the type 'option' then 
   it can be bottom or top 

   defining a lattice as a module type with parameters 
      http://people.irisa.fr/David.Pichardie/ext/these/HTML/chap4.lattice_def.html

   defining a lattice as a class 
        https://github.com/coq-contribs/relation-algebra/blob/master/lattice.v

   resource used to outline the lattice Module 
        http://www.cs.ox.ac.uk/people/daniel.james/lattice/lattice.pdf
 *)

Require Import Poset.  

Module Type Lattice.

  (* A lattice is a set, t *)
  Parameter t : Set. 
  Parameter eq : t -> t -> Prop.

  (* With two binary operators, meet and join *)
  Parameter join : t -> t -> t.
  Parameter meet : t -> t -> t. 

  (* With the following identities 
        communtative, associative, absorptive, and idempotent *)
  Axiom meet_commutative : forall a b, meet a b = meet b a. 
  Axiom join_communative : forall a b, join a b = join b a.

  Axiom meet_associative : forall a b c, meet (meet a b) c = meet a (meet b c).
  Axiom join_associative : forall a b c, join (join a b) c = join a (join b c).

  Axiom meet_absorptive : forall a b, meet a (join a b) = a.
  Axiom join_absorptive : forall a b, join a (meet a b) = a. 

  Axiom meet_idempotent : forall a, meet a a = a.
  Axiom join_idempotent : forall a, join a a = a. 

End Lattice.


  (* What properties do we need? 

  - intersection
  - subterms 
  

 *)



  
