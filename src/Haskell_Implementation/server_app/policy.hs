module Policy where

import qualified Prelude



checkPolicy :: Term -> Plc -> Environment -> Bool
checkPolicy (Coq_asp a) k e = checkASPPolicy k a e
checkPolicy (Coq_att p t) k e = checkPolicy t p e
checkPolicy (Coq_lseq t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e
checkPolicy (Coq_bseq _ t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e
checkPolicy (Coq_bpar _ t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e