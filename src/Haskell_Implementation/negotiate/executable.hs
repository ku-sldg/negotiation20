module Executable where

import Prelude
import Copland
import Manifest

-- Does Plc (p) know of Plc (k) in Environment (e) 
knowsOfe :: Plc -> Plc -> Environment -> Bool
knowsOfe p k e =
  case lookup k e of
    Nothing -> False
    Just (Build_Manifest _ places _)  -> p `elem` places

hasASPe :: Int -> ASP -> Environment -> Bool
hasASPe k a e =
  case lookup k e of
    Nothing -> False
    Just (Build_Manifest asps _ _)  -> a `elem` asps -- checks to see that a is in the asps

-- is term t executable on place p in environment e
executable :: Term -> Plc -> Environment -> Bool
executable (Coq_asp a) k e = hasASPe k a e
executable (Coq_att p t) k e = knowsOfe p k e && executable t p e
executable (Coq_lseq t1 t2) k e = executable t1 k e && executable t2 k e
executable (Coq_bseq _ t1 t2) k e = executable t1 k e && executable t2 k e
executable (Coq_bpar _ t1 t2) k e = executable t1 k e && executable t2 k e