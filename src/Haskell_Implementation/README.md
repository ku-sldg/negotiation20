Extraction of NFM code from Coq to Haskell 

## Dependencies 

1. Coq
2. Haskell 

## Process to generate Haskell Code from Coq

Follow these steps to generate code file by file
1. Comment out modules 
2. Add the following to your .v file you wish to extract 

Require Import ExtrHaskellBasic. 
Extraction Language Haskell.
Extraction "fileName.hs" functionToExport. 

where fileName is where the output code with be and functionToExport is the name of the function which you want extracted. Extraction will also output all the function's dependencies. 

3. type `coqc fileName.v` into the terminal to perform the extraction. 

4. You shoudl see a fileName.hs in the folder where you performed the extraction