module Policy where

import Prelude
import Copland
import Manifest

-- Check environment [e] and see if place [p] has some policy 
-- where the Policy allows p to run a. *)
checkASPPolicy :: Plc -> Plc -> Environment -> ASP -> Bool
checkASPPolicy req_p rec_p e a =
  case lookup rec_p e of
    Nothing -> False
    Just (Build_Manifest _ _ policies)  -> (a, req_p) `elem` policies

checkPolicy :: Term -> Plc -> Plc -> Environment -> Bool
checkPolicy (Coq_asp a) req_p rec_p e = checkASPPolicy req_p rec_p e a
checkPolicy (Coq_att p t) req_p rec_p e = checkPolicy t req_p p e
checkPolicy (Coq_lseq t1 t2) req_p rec_p e = checkPolicy t1 req_p rec_p e && checkPolicy t2 req_p rec_p e
checkPolicy (Coq_bseq _ t1 t2) req_p rec_p e = checkPolicy t1 req_p rec_p e && checkPolicy t2 req_p rec_p e
checkPolicy (Coq_bpar _ t1 t2) req_p rec_p e = checkPolicy t1 req_p rec_p e && checkPolicy t2 req_p rec_p e