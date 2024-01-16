module Policy where

import Prelude
import Copland
import Manifest

checkASPPolicy :: Plc -> ASP -> Environment -> Bool
checkASPPolicy k a e =
  case lookup k e of
    Nothing -> False
    Just (Build_Manifest _ _ policies)  -> True

checkPolicy :: Term -> Plc -> Environment -> Bool
checkPolicy (Coq_asp a) k e = checkASPPolicy k a e
checkPolicy (Coq_att p t) k e = checkPolicy t p e
checkPolicy (Coq_lseq t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e
checkPolicy (Coq_bseq _ t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e
checkPolicy (Coq_bpar _ t1 t2) k e = checkPolicy t1 k e && checkPolicy t2 k e