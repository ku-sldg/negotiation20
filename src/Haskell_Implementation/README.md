# Negotiation stub for Remote Attestation 

This is a Haskell implementation of a negotiation stub. This stub would be placed on a target system. It has abstract manifests in the `system_spec.hs` file which are reasoned about in `policy.hs` and `exectuable.hs`. These executability and policy checks are called from a main function in negotiate.hs

## To Run

1. cd into the negotiate folder 
2. type `make`
3. type `./negotiate`

## Dependencies 

1. Coq
2. Haskell 

## Process to generate Haskell Code from Coq

Most of the code is handwritten but if you wanted to use the code extraction tool from Haskell simply add the following code the the bottom of the file you wish to extract. 

    Require Import ExtrHaskellBasic. 
    Extraction Language Haskell.
    Extraction "fileName.hs" functionToExport. 

where fileName is where the output code with be and functionToExport is the name of the function which you want extracted. Extraction will also output all the function's dependencies. 

Then type compile the coq file using `coqc` or `make` if there is an `_CoqProject`

All generated code was place in the `extracted_src` folder. 
