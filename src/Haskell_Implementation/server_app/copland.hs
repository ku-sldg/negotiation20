module Copland where

import Prelude

type Plc = Prelude.Int

type N_ID = Prelude.Int

type Event_ID = Prelude.Int

type ASP_ID = Prelude.Int

type TARG_ID = Prelude.Int

type Arg = Prelude.String

type ASP_PARAMS = String

--data ASP_PARAMS =
--   Coq_asp_paramsC ASP_ID (([]) Arg) Plc TARG_ID

data ASP =
   CPY
 | ASPC ASP_PARAMS
 | SIG
 | HSH
 deriving (Eq)

data SP =
   ALL
 | NONE

type Split = (,) SP SP

data Term =
   Coq_asp ASP
 | Coq_att Plc Term
 | Coq_lseq Term Term
 | Coq_bseq Split Term Term
 | Coq_bpar Split Term Term

{-- instance Show ASP_PARAMS where
    show (Coq_asp_paramsC aspId args plc targId) =
        "Coq_asp_paramsC " ++ show aspId ++ " " ++ show args ++ " " ++ show plc ++ " " ++ show targId --}

instance Show ASP where
   show CPY = "CPY"
   show (ASPC params) = "ASPC " ++ show params
   show SIG = "SIG"
   show HSH = "HSH"

instance Show Term where
   show (Coq_asp asp) = "Coq_asp " ++ show asp
   show (Coq_att plc term) = "Coq_att " ++ show plc ++ " " ++ show term
   show (Coq_lseq t1 t2) = "Coq_lseq " ++ show t1 ++ " " ++ show t2
   show (Coq_bseq split t1 t2) = "Coq_bseq " ++ show t1 ++ " " ++ show t2
   show (Coq_bpar split t1 t2) = "Coq_bpar " ++ show t1 ++ " " ++ show t2
