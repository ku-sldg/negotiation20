module Copland where

import qualified Prelude

data Nat =
   O
 | S Nat

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

data String =
   EmptyString
 | String0 Ascii0 String

type Plc = String

type N_ID = Nat

type ASP_ID = String

type TARG_ID = String

type Arg = String

data ASP_PARAMS =
   Asp_paramsC ASP_ID (([]) Arg) Plc TARG_ID

data FWD =
   COMP
 | ENCR
 | EXTD
 | KILL
 | KEEP

data SP =
   ALL
 | NONE

data ASP =
   NULL
 | CPY
 | ASPC SP FWD ASP_PARAMS
 | SIG
 | HSH

type Split = (,) SP SP

data Term =
   Asp ASP
 | Att Plc Term
 | Lseq Term Term
 | Bseq Split Term Term
 | Bpar Split Term Term

data Evidence =
   Mt
 | Nn N_ID
 | Uu Plc FWD ASP_PARAMS Evidence
 | Ss Evidence Evidence

sig_params :: ASP_PARAMS
sig_params =
  Prelude.error "AXIOM TO BE REALIZED"

hsh_params :: ASP_PARAMS
hsh_params =
  Prelude.error "AXIOM TO BE REALIZED"

sp_ev :: SP -> Evidence -> Evidence
sp_ev sp e =
  case sp of {
   ALL -> e;
   NONE -> Mt}

eval_asp :: ASP -> Plc -> Evidence -> Evidence
eval_asp t p e =
  case t of {
   NULL -> Mt;
   CPY -> e;
   ASPC sp fwd params ->
    case fwd of {
     KILL -> Mt;
     KEEP -> sp_ev sp e;
     _ -> Uu p fwd params (sp_ev sp e)};
   SIG -> Uu p EXTD sig_params e;
   HSH -> Uu p COMP hsh_params e}

splitEv_T_l :: Split -> Evidence -> Evidence
splitEv_T_l sp e =
  case sp of {
   (,) s _ -> case s of {
               ALL -> e;
               NONE -> Mt}}

splitEv_T_r :: Split -> Evidence -> Evidence
splitEv_T_r sp e =
  case sp of {
   (,) _ s0 -> case s0 of {
                ALL -> e;
                NONE -> Mt}}

eval :: Term -> Plc -> Evidence -> Evidence
eval t p e =
  case t of {
   Asp a -> eval_asp a p e;
   Att q t1 -> eval t1 q e;
   Lseq t1 t2 -> eval t2 p (eval t1 p e);
   Bseq s t1 t2 -> Ss (eval t1 p (splitEv_T_l s e))
    (eval t2 p (splitEv_T_r s e));
   Bpar s t1 t2 -> Ss (eval t1 p (splitEv_T_l s e))
    (eval t2 p (splitEv_T_r s e))}

