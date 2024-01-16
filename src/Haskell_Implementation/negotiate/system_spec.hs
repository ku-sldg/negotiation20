module System_spec where

import Copland
import Manifest

-- asps
aVC :: ASP 
aVC = ASPC ("vc")

aSFS :: ASP 
aSFS = ASPC ("sfs")

-- Manifests
-- Build_Manifest [ASP] [Plc] [(ASP,Plc)]
e_P0 :: Manifest
e_P0 = Build_Manifest ([]) ([1]) ([])

e_P1 :: Manifest
e_P1 = Build_Manifest ([aVC, HSH]) ([2]) ([])

e_P2 :: Manifest
e_P2 = Build_Manifest ([aSFS]) ([1]) ([])

targ_env :: Environment
targ_env = [(0, e_P0), (1, e_P1), (2, e_P2)]