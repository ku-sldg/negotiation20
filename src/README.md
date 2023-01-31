# All code relating to negotiation exists here. 

All formal models are realized in Coq with version 8.16.0. 

## `ISAKMP`

Information pertaining to ISAKMP security association. Nothing to prove here yet... 

## `Refinement` 

Formal models pertaining to refinement. Includes definition of manfiests and proofs of executability. Also includes soundness definitions and proofs. 

TODO: protocol generation

## `Selection` 

Formal models of interest describe protocol orderings. We believe that the protocols can be ordered to form a lattice whereby the top of the lattice is the situationally best protocol. 

TODO: instantiate lattice and prove properties

## `DeptTypes` 

All code from "A Type Dependent Policy Language". This include a dependently typed privacy policy and selection policy for the target. This is information relative to Fritz thesis (2019). 
