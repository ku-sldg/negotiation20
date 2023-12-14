Extraction of NFM code from Coq to Haskell 

## Dependencies 

1. Coq
2. Haskell 

## Process to generate Haskell Code from Coq

Simply add the following code the the bottom of the file you wish to extract. 

Require Import ExtrHaskellBasic. 
Extraction Language Haskell.
Extraction "fileName.hs" functionToExport. 

where fileName is where the output code with be and functionToExport is the name of the function which you want extracted. Extraction will also output all the function's dependencies. 

Then type compile the coq file using `coqc` or `make` if there is an `_CoqProject`
