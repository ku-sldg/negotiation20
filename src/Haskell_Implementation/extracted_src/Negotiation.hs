module Negotiation where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   Prelude.True -> f;
   Prelude.False -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

bool_dec :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
bool_dec b1 b2 =
  bool_rec (\x ->
    case x of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) (\x ->
    case x of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) b1 b2

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

ascii_rect :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii b b0 b1 b2 b3 b4 b5 b6 -> f b b0 b1 b2 b3 b4 b5 b6}

ascii_rec :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Prelude.Bool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                      (bool_dec b7 b15)) (\_ -> Prelude.False)
                    (bool_dec b6 b14)) (\_ -> Prelude.False)
                  (bool_dec b5 b13)) (\_ -> Prelude.False) (bool_dec b4 b12))
              (\_ -> Prelude.False) (bool_dec b3 b11)) (\_ -> Prelude.False)
            (bool_dec b2 b10)) (\_ -> Prelude.False) (bool_dec b1 b9)) (\_ ->
        Prelude.False) (bool_dec b0 b8)}) a b

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Prelude.Bool
string_dec s1 s2 =
  string_rec (\x ->
    case x of {
     EmptyString -> Prelude.True;
     String0 _ _ -> Prelude.False}) (\a _ x x0 ->
    case x0 of {
     EmptyString -> Prelude.False;
     String0 a0 s ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x s)) (\_ ->
        Prelude.False) (ascii_dec a a0)}) s1 s2

type Plc = String

type ASP_ID = String

type TARG_ID = String

type Arg = String

data ASP_PARAMS =
   Asp_paramsC ASP_ID (([]) Arg) Plc TARG_ID

aSP_PARAMS_rect :: (ASP_ID -> (([]) Arg) -> Plc -> TARG_ID -> a1) ->
                   ASP_PARAMS -> a1
aSP_PARAMS_rect f a =
  case a of {
   Asp_paramsC a0 l p t -> f a0 l p t}

aSP_PARAMS_rec :: (ASP_ID -> (([]) Arg) -> Plc -> TARG_ID -> a1) ->
                  ASP_PARAMS -> a1
aSP_PARAMS_rec =
  aSP_PARAMS_rect

data FWD =
   COMP
 | ENCR
 | EXTD
 | KILL
 | KEEP

fWD_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> FWD -> a1
fWD_rect f f0 f1 f2 f3 f4 =
  case f4 of {
   COMP -> f;
   ENCR -> f0;
   EXTD -> f1;
   KILL -> f2;
   KEEP -> f3}

fWD_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> FWD -> a1
fWD_rec =
  fWD_rect

data SP =
   ALL
 | NONE

sP_rect :: a1 -> a1 -> SP -> a1
sP_rect f f0 s =
  case s of {
   ALL -> f;
   NONE -> f0}

sP_rec :: a1 -> a1 -> SP -> a1
sP_rec =
  sP_rect

data ASP =
   NULL
 | CPY
 | ASPC SP FWD ASP_PARAMS
 | SIG
 | HSH

aSP_rect :: a1 -> a1 -> (SP -> FWD -> ASP_PARAMS -> a1) -> a1 -> a1 -> ASP ->
            a1
aSP_rect f f0 f1 f2 f3 a =
  case a of {
   NULL -> f;
   CPY -> f0;
   ASPC s f4 a0 -> f1 s f4 a0;
   SIG -> f2;
   HSH -> f3}

aSP_rec :: a1 -> a1 -> (SP -> FWD -> ASP_PARAMS -> a1) -> a1 -> a1 -> ASP ->
           a1
aSP_rec =
  aSP_rect

aSP_dec :: ASP -> ASP -> Prelude.Bool
aSP_dec a1 a2 =
  aSP_rec (\x -> case x of {
                  NULL -> Prelude.True;
                  _ -> Prelude.False}) (\x ->
    case x of {
     CPY -> Prelude.True;
     _ -> Prelude.False}) (\s f a x ->
    case x of {
     ASPC s0 f0 a0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (aSP_PARAMS_rec (\a3 l p t x0 ->
              case x0 of {
               Asp_paramsC a4 l0 p0 t0 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                        (string_rec (\x1 ->
                          case x1 of {
                           EmptyString -> Prelude.True;
                           String0 _ _ -> Prelude.False}) (\a5 _ x1 x2 ->
                          case x2 of {
                           EmptyString -> Prelude.False;
                           String0 a6 s1 ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ -> Prelude.True) (\_ ->
                                Prelude.False) (x1 s1)) (\_ -> Prelude.False)
                              (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                                case x3 of {
                                 Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                sumbool_rec (\_ ->
                                                  Prelude.True) (\_ ->
                                                  Prelude.False)
                                                  (bool_rec (\x4 ->
                                                    case x4 of {
                                                     Prelude.True ->
                                                      Prelude.True;
                                                     Prelude.False ->
                                                      Prelude.False}) (\x4 ->
                                                    case x4 of {
                                                     Prelude.True ->
                                                      Prelude.False;
                                                     Prelude.False ->
                                                      Prelude.True}) b6 b14))
                                                (\_ -> Prelude.False)
                                                (bool_rec (\x4 ->
                                                  case x4 of {
                                                   Prelude.True ->
                                                    Prelude.True;
                                                   Prelude.False ->
                                                    Prelude.False}) (\x4 ->
                                                  case x4 of {
                                                   Prelude.True ->
                                                    Prelude.False;
                                                   Prelude.False ->
                                                    Prelude.True}) b5 b13))
                                              (\_ -> Prelude.False)
                                              (bool_rec (\x4 ->
                                                case x4 of {
                                                 Prelude.True -> Prelude.True;
                                                 Prelude.False ->
                                                  Prelude.False}) (\x4 ->
                                                case x4 of {
                                                 Prelude.True ->
                                                  Prelude.False;
                                                 Prelude.False ->
                                                  Prelude.True}) b4 b12))
                                            (\_ -> Prelude.False)
                                            (bool_rec (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.True;
                                               Prelude.False -> Prelude.False})
                                              (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.False;
                                               Prelude.False -> Prelude.True})
                                              b3 b11)) (\_ -> Prelude.False)
                                          (bool_rec (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b2 b10)) (\_ -> Prelude.False)
                                        (bool_rec (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b1
                                          b9)) (\_ -> Prelude.False)
                                      (bool_rec (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b0
                                        b8)) (\_ -> Prelude.False)
                                    (bool_rec (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b b7)})
                                a5 a6)}) t t0)) (\_ -> Prelude.False)
                      (string_rec (\x1 ->
                        case x1 of {
                         EmptyString -> Prelude.True;
                         String0 _ _ -> Prelude.False}) (\a5 _ x1 x2 ->
                        case x2 of {
                         EmptyString -> Prelude.False;
                         String0 a6 s1 ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ -> Prelude.True) (\_ ->
                              Prelude.False) (x1 s1)) (\_ -> Prelude.False)
                            (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                              case x3 of {
                               Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                Prelude.True) (\_ ->
                                                Prelude.False)
                                                (bool_rec (\x4 ->
                                                  case x4 of {
                                                   Prelude.True ->
                                                    Prelude.True;
                                                   Prelude.False ->
                                                    Prelude.False}) (\x4 ->
                                                  case x4 of {
                                                   Prelude.True ->
                                                    Prelude.False;
                                                   Prelude.False ->
                                                    Prelude.True}) b6 b14))
                                              (\_ -> Prelude.False)
                                              (bool_rec (\x4 ->
                                                case x4 of {
                                                 Prelude.True -> Prelude.True;
                                                 Prelude.False ->
                                                  Prelude.False}) (\x4 ->
                                                case x4 of {
                                                 Prelude.True ->
                                                  Prelude.False;
                                                 Prelude.False ->
                                                  Prelude.True}) b5 b13))
                                            (\_ -> Prelude.False)
                                            (bool_rec (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.True;
                                               Prelude.False -> Prelude.False})
                                              (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.False;
                                               Prelude.False -> Prelude.True})
                                              b4 b12)) (\_ -> Prelude.False)
                                          (bool_rec (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b3 b11)) (\_ -> Prelude.False)
                                        (bool_rec (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b2
                                          b10)) (\_ -> Prelude.False)
                                      (bool_rec (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b1
                                        b9)) (\_ -> Prelude.False)
                                    (bool_rec (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b0 b8))
                                  (\_ -> Prelude.False)
                                  (bool_rec (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b b7)})
                              a5 a6)}) p p0)) (\_ -> Prelude.False)
                    (list_rec (\x1 ->
                      case x1 of {
                       ([]) -> Prelude.True;
                       (:) _ _ -> Prelude.False}) (\a5 _ x1 x2 ->
                      case x2 of {
                       ([]) -> Prelude.False;
                       (:) a6 l1 ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False) (x1 l1)) (\_ -> Prelude.False)
                          (string_rec (\x3 ->
                            case x3 of {
                             EmptyString -> Prelude.True;
                             String0 _ _ -> Prelude.False}) (\a7 _ x3 x4 ->
                            case x4 of {
                             EmptyString -> Prelude.False;
                             String0 a8 s1 ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ -> Prelude.True) (\_ ->
                                  Prelude.False) (x3 s1)) (\_ ->
                                Prelude.False)
                                (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x5 ->
                                  case x5 of {
                                   Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                sumbool_rec (\_ ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False)
                                                    (bool_rec (\x6 ->
                                                      case x6 of {
                                                       Prelude.True ->
                                                        Prelude.True;
                                                       Prelude.False ->
                                                        Prelude.False})
                                                      (\x6 ->
                                                      case x6 of {
                                                       Prelude.True ->
                                                        Prelude.False;
                                                       Prelude.False ->
                                                        Prelude.True}) b6
                                                      b14)) (\_ ->
                                                  Prelude.False)
                                                  (bool_rec (\x6 ->
                                                    case x6 of {
                                                     Prelude.True ->
                                                      Prelude.True;
                                                     Prelude.False ->
                                                      Prelude.False}) (\x6 ->
                                                    case x6 of {
                                                     Prelude.True ->
                                                      Prelude.False;
                                                     Prelude.False ->
                                                      Prelude.True}) b5 b13))
                                                (\_ -> Prelude.False)
                                                (bool_rec (\x6 ->
                                                  case x6 of {
                                                   Prelude.True ->
                                                    Prelude.True;
                                                   Prelude.False ->
                                                    Prelude.False}) (\x6 ->
                                                  case x6 of {
                                                   Prelude.True ->
                                                    Prelude.False;
                                                   Prelude.False ->
                                                    Prelude.True}) b4 b12))
                                              (\_ -> Prelude.False)
                                              (bool_rec (\x6 ->
                                                case x6 of {
                                                 Prelude.True -> Prelude.True;
                                                 Prelude.False ->
                                                  Prelude.False}) (\x6 ->
                                                case x6 of {
                                                 Prelude.True ->
                                                  Prelude.False;
                                                 Prelude.False ->
                                                  Prelude.True}) b3 b11))
                                            (\_ -> Prelude.False)
                                            (bool_rec (\x6 ->
                                              case x6 of {
                                               Prelude.True -> Prelude.True;
                                               Prelude.False -> Prelude.False})
                                              (\x6 ->
                                              case x6 of {
                                               Prelude.True -> Prelude.False;
                                               Prelude.False -> Prelude.True})
                                              b2 b10)) (\_ -> Prelude.False)
                                          (bool_rec (\x6 ->
                                            case x6 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x6 ->
                                            case x6 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b1 b9)) (\_ -> Prelude.False)
                                        (bool_rec (\x6 ->
                                          case x6 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x6 ->
                                          case x6 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b0
                                          b8)) (\_ -> Prelude.False)
                                      (bool_rec (\x6 ->
                                        case x6 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x6 ->
                                        case x6 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b
                                        b7)}) a7 a8)}) a5 a6)}) l l0)) (\_ ->
                  Prelude.False)
                  (string_rec (\x1 ->
                    case x1 of {
                     EmptyString -> Prelude.True;
                     String0 _ _ -> Prelude.False}) (\a5 _ x1 x2 ->
                    case x2 of {
                     EmptyString -> Prelude.False;
                     String0 a6 s1 ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ -> Prelude.True) (\_ ->
                          Prelude.False) (x1 s1)) (\_ -> Prelude.False)
                        (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                          case x3 of {
                           Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ -> Prelude.True)
                                            (\_ -> Prelude.False)
                                            (bool_rec (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.True;
                                               Prelude.False -> Prelude.False})
                                              (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.False;
                                               Prelude.False -> Prelude.True})
                                              b6 b14)) (\_ -> Prelude.False)
                                          (bool_rec (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b5 b13)) (\_ -> Prelude.False)
                                        (bool_rec (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b4
                                          b12)) (\_ -> Prelude.False)
                                      (bool_rec (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b3
                                        b11)) (\_ -> Prelude.False)
                                    (bool_rec (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b2
                                      b10)) (\_ -> Prelude.False)
                                  (bool_rec (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b1 b9))
                                (\_ -> Prelude.False)
                                (bool_rec (\x4 ->
                                  case x4 of {
                                   Prelude.True -> Prelude.True;
                                   Prelude.False -> Prelude.False}) (\x4 ->
                                  case x4 of {
                                   Prelude.True -> Prelude.False;
                                   Prelude.False -> Prelude.True}) b0 b8))
                              (\_ -> Prelude.False)
                              (bool_rec (\x4 ->
                                case x4 of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> Prelude.False}) (\x4 ->
                                case x4 of {
                                 Prelude.True -> Prelude.False;
                                 Prelude.False -> Prelude.True}) b b7)}) a5
                          a6)}) a3 a4)}) a a0)) (\_ -> Prelude.False)
          (fWD_rec (\x0 ->
            case x0 of {
             COMP -> Prelude.True;
             _ -> Prelude.False}) (\x0 ->
            case x0 of {
             ENCR -> Prelude.True;
             _ -> Prelude.False}) (\x0 ->
            case x0 of {
             EXTD -> Prelude.True;
             _ -> Prelude.False}) (\x0 ->
            case x0 of {
             KILL -> Prelude.True;
             _ -> Prelude.False}) (\x0 ->
            case x0 of {
             KEEP -> Prelude.True;
             _ -> Prelude.False}) f f0)) (\_ -> Prelude.False)
        (sP_rec (\x0 ->
          case x0 of {
           ALL -> Prelude.True;
           NONE -> Prelude.False}) (\x0 ->
          case x0 of {
           ALL -> Prelude.False;
           NONE -> Prelude.True}) s s0);
     _ -> Prelude.False}) (\x ->
    case x of {
     SIG -> Prelude.True;
     _ -> Prelude.False}) (\x ->
    case x of {
     HSH -> Prelude.True;
     _ -> Prelude.False}) a1 a2

type Split = (,) SP SP

data Term =
   Asp ASP
 | Att Plc Term
 | Lseq Term Term
 | Bseq Split Term Term
 | Bpar Split Term Term

term_rect :: (ASP -> a1) -> (Plc -> Term -> a1 -> a1) -> (Term -> a1 -> Term
             -> a1 -> a1) -> (Split -> Term -> a1 -> Term -> a1 -> a1) ->
             (Split -> Term -> a1 -> Term -> a1 -> a1) -> Term -> a1
term_rect f f0 f1 f2 f3 t =
  case t of {
   Asp a -> f a;
   Att p t0 -> f0 p t0 (term_rect f f0 f1 f2 f3 t0);
   Lseq t0 t1 ->
    f1 t0 (term_rect f f0 f1 f2 f3 t0) t1 (term_rect f f0 f1 f2 f3 t1);
   Bseq s t0 t1 ->
    f2 s t0 (term_rect f f0 f1 f2 f3 t0) t1 (term_rect f f0 f1 f2 f3 t1);
   Bpar s t0 t1 ->
    f3 s t0 (term_rect f f0 f1 f2 f3 t0) t1 (term_rect f f0 f1 f2 f3 t1)}

term_rec :: (ASP -> a1) -> (Plc -> Term -> a1 -> a1) -> (Term -> a1 -> Term
            -> a1 -> a1) -> (Split -> Term -> a1 -> Term -> a1 -> a1) ->
            (Split -> Term -> a1 -> Term -> a1 -> a1) -> Term -> a1
term_rec =
  term_rect

data Manifest =
   Build_Manifest (([]) ASP) (([]) Plc) (([]) Plc)

asps :: Manifest -> ([]) ASP
asps m =
  case m of {
   Build_Manifest asps0 _ _ -> asps0}

k :: Manifest -> ([]) Plc
k m =
  case m of {
   Build_Manifest _ k0 _ -> k0}

type Environment = Plc -> Prelude.Maybe Manifest

e_empty :: Environment
e_empty _ =
  Prelude.Nothing

e_update :: Environment -> Plc -> (Prelude.Maybe Manifest) -> String ->
            Prelude.Maybe Manifest
e_update m x v x' =
  case string_dec x x' of {
   Prelude.True -> v;
   Prelude.False -> m x'}

hasASPe_dec :: Plc -> Environment -> ASP -> Prelude.Bool
hasASPe_dec k0 e a =
  let {o = e k0} in
  case o of {
   Prelude.Just m ->
    let {l = asps m} in
    list_rec Prelude.False (\a0 _ iHl ->
      case iHl of {
       Prelude.True -> Prelude.True;
       Prelude.False ->
        let {
         asp_dec = aSP_rec (\x ->
                     case x of {
                      NULL -> Prelude.True;
                      _ -> Prelude.False}) (\x ->
                     case x of {
                      CPY -> Prelude.True;
                      _ -> Prelude.False}) (\s f a1 x ->
                     case x of {
                      ASPC s0 f0 a2 ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ -> Prelude.True) (\_ ->
                             Prelude.False)
                             (aSP_PARAMS_rec (\a3 l0 p t x0 ->
                               case x0 of {
                                Asp_paramsC a4 l1 p0 t0 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ -> Prelude.True)
                                         (\_ -> Prelude.False)
                                         (string_rec (\x1 ->
                                           case x1 of {
                                            EmptyString -> Prelude.True;
                                            String0 _ _ -> Prelude.False})
                                           (\a5 _ x1 x2 ->
                                           case x2 of {
                                            EmptyString -> Prelude.False;
                                            String0 a6 s1 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False) (x1 s1))
                                               (\_ -> Prelude.False)
                                               (ascii_rec
                                                 (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                                                 case x3 of {
                                                  Ascii b7 b8 b9 b10 b11 b12
                                                   b13 b14 ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 sumbool_rec
                                                                   (\_ ->
                                                                   Prelude.True)
                                                                   (\_ ->
                                                                   Prelude.False)
                                                                   (bool_rec
                                                                    (\x4 ->
                                                                    case x4 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x4 ->
                                                                    case x4 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x4 ->
                                                                   case x4 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x4 ->
                                                                   case x4 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b5 b13))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x4 ->
                                                                 case x4 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x4 ->
                                                                 case x4 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b4 b12))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b3 b11))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b2 b10)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b1 b9)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b0
                                                         b8)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b b7)})
                                                 a5 a6)}) t t0)) (\_ ->
                                       Prelude.False)
                                       (string_rec (\x1 ->
                                         case x1 of {
                                          EmptyString -> Prelude.True;
                                          String0 _ _ -> Prelude.False})
                                         (\a5 _ x1 x2 ->
                                         case x2 of {
                                          EmptyString -> Prelude.False;
                                          String0 a6 s1 ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ -> Prelude.True)
                                               (\_ -> Prelude.False) 
                                               (x1 s1)) (\_ -> Prelude.False)
                                             (ascii_rec
                                               (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                                               case x3 of {
                                                Ascii b7 b8 b9 b10 b11 b12
                                                 b13 b14 ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 Prelude.True)
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x4 ->
                                                                   case x4 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x4 ->
                                                                   case x4 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b6 b14))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x4 ->
                                                                 case x4 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x4 ->
                                                                 case x4 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b5 b13))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b4 b12))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b3 b11)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b2 b10)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b1
                                                         b9)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b0
                                                       b8)) (\_ ->
                                                   Prelude.False)
                                                   (bool_rec (\x4 ->
                                                     case x4 of {
                                                      Prelude.True ->
                                                       Prelude.True;
                                                      Prelude.False ->
                                                       Prelude.False})
                                                     (\x4 ->
                                                     case x4 of {
                                                      Prelude.True ->
                                                       Prelude.False;
                                                      Prelude.False ->
                                                       Prelude.True}) b b7)})
                                               a5 a6)}) p p0)) (\_ ->
                                     Prelude.False)
                                     (list_rec (\x1 ->
                                       case x1 of {
                                        ([]) -> Prelude.True;
                                        (:) _ _ -> Prelude.False})
                                       (\a5 _ x1 x2 ->
                                       case x2 of {
                                        ([]) -> Prelude.False;
                                        (:) a6 l2 ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ -> Prelude.True)
                                             (\_ -> Prelude.False) (x1 l2))
                                           (\_ -> Prelude.False)
                                           (string_rec (\x3 ->
                                             case x3 of {
                                              EmptyString -> Prelude.True;
                                              String0 _ _ -> Prelude.False})
                                             (\a7 _ x3 x4 ->
                                             case x4 of {
                                              EmptyString -> Prelude.False;
                                              String0 a8 s1 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   Prelude.True) (\_ ->
                                                   Prelude.False) (x3 s1))
                                                 (\_ -> Prelude.False)
                                                 (ascii_rec
                                                   (\b b0 b1 b2 b3 b4 b5 b6 x5 ->
                                                   case x5 of {
                                                    Ascii b7 b8 b9 b10 b11
                                                     b12 b13 b14 ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 sumbool_rec
                                                                   (\_ ->
                                                                   sumbool_rec
                                                                    (\_ ->
                                                                    Prelude.True)
                                                                    (\_ ->
                                                                    Prelude.False)
                                                                    (bool_rec
                                                                    (\x6 ->
                                                                    case x6 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x6 ->
                                                                    case x6 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                   (\_ ->
                                                                   Prelude.False)
                                                                   (bool_rec
                                                                    (\x6 ->
                                                                    case x6 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x6 ->
                                                                    case x6 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b5 b13))
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x6 ->
                                                                   case x6 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x6 ->
                                                                   case x6 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b4 b12))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x6 ->
                                                                 case x6 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x6 ->
                                                                 case x6 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b3 b11))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x6 ->
                                                               case x6 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x6 ->
                                                               case x6 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b2 b10))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x6 ->
                                                             case x6 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x6 ->
                                                             case x6 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b1 b9)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x6 ->
                                                           case x6 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x6 ->
                                                           case x6 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b0 b8)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x6 ->
                                                         case x6 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x6 ->
                                                         case x6 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b
                                                         b7)}) a7 a8)}) a5
                                             a6)}) l0 l1)) (\_ ->
                                   Prelude.False)
                                   (string_rec (\x1 ->
                                     case x1 of {
                                      EmptyString -> Prelude.True;
                                      String0 _ _ -> Prelude.False})
                                     (\a5 _ x1 x2 ->
                                     case x2 of {
                                      EmptyString -> Prelude.False;
                                      String0 a6 s1 ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False) (x1 s1))
                                         (\_ -> Prelude.False)
                                         (ascii_rec
                                           (\b b0 b1 b2 b3 b4 b5 b6 x3 ->
                                           case x3 of {
                                            Ascii b7 b8 b9 b10 b11 b12 b13
                                             b14 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             Prelude.True)
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x4 ->
                                                               case x4 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b6 b14))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x4 ->
                                                             case x4 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b5 b13)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x4 ->
                                                           case x4 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b4 b12)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x4 ->
                                                         case x4 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b3
                                                         b11)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x4 ->
                                                       case x4 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b2
                                                       b10)) (\_ ->
                                                   Prelude.False)
                                                   (bool_rec (\x4 ->
                                                     case x4 of {
                                                      Prelude.True ->
                                                       Prelude.True;
                                                      Prelude.False ->
                                                       Prelude.False})
                                                     (\x4 ->
                                                     case x4 of {
                                                      Prelude.True ->
                                                       Prelude.False;
                                                      Prelude.False ->
                                                       Prelude.True}) b1 b9))
                                                 (\_ -> Prelude.False)
                                                 (bool_rec (\x4 ->
                                                   case x4 of {
                                                    Prelude.True ->
                                                     Prelude.True;
                                                    Prelude.False ->
                                                     Prelude.False}) (\x4 ->
                                                   case x4 of {
                                                    Prelude.True ->
                                                     Prelude.False;
                                                    Prelude.False ->
                                                     Prelude.True}) b0 b8))
                                               (\_ -> Prelude.False)
                                               (bool_rec (\x4 ->
                                                 case x4 of {
                                                  Prelude.True ->
                                                   Prelude.True;
                                                  Prelude.False ->
                                                   Prelude.False}) (\x4 ->
                                                 case x4 of {
                                                  Prelude.True ->
                                                   Prelude.False;
                                                  Prelude.False ->
                                                   Prelude.True}) b b7)}) a5
                                           a6)}) a3 a4)}) a1 a2)) (\_ ->
                           Prelude.False)
                           (fWD_rec (\x0 ->
                             case x0 of {
                              COMP -> Prelude.True;
                              _ -> Prelude.False}) (\x0 ->
                             case x0 of {
                              ENCR -> Prelude.True;
                              _ -> Prelude.False}) (\x0 ->
                             case x0 of {
                              EXTD -> Prelude.True;
                              _ -> Prelude.False}) (\x0 ->
                             case x0 of {
                              KILL -> Prelude.True;
                              _ -> Prelude.False}) (\x0 ->
                             case x0 of {
                              KEEP -> Prelude.True;
                              _ -> Prelude.False}) f f0)) (\_ ->
                         Prelude.False)
                         (sP_rec (\x0 ->
                           case x0 of {
                            ALL -> Prelude.True;
                            NONE -> Prelude.False}) (\x0 ->
                           case x0 of {
                            ALL -> Prelude.False;
                            NONE -> Prelude.True}) s s0);
                      _ -> Prelude.False}) (\x ->
                     case x of {
                      SIG -> Prelude.True;
                      _ -> Prelude.False}) (\x ->
                     case x of {
                      HSH -> Prelude.True;
                      _ -> Prelude.False}) a a0}
        in
        case asp_dec of {
         Prelude.True -> eq_rec_r a0 (\_ _ -> Prelude.True) a __ asp_dec;
         Prelude.False -> Prelude.False}}) l;
   Prelude.Nothing -> Prelude.False}

knowsOfe_dec :: Plc -> Environment -> Plc -> Prelude.Bool
knowsOfe_dec k0 e p =
  let {o = e k0} in
  case o of {
   Prelude.Just m ->
    let {l = k m} in
    list_rec Prelude.False (\a _ iHl ->
      let {
       h = string_rec (\x ->
             case x of {
              EmptyString -> Prelude.True;
              String0 _ _ -> Prelude.False}) (\a0 _ x x0 ->
             case x0 of {
              EmptyString -> Prelude.False;
              String0 a1 s ->
               sumbool_rec (\_ ->
                 sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x s))
                 (\_ -> Prelude.False)
                 (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                   case x1 of {
                    Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                     sumbool_rec (\_ ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ ->
                             sumbool_rec (\_ ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ -> Prelude.True) (\_ ->
                                     Prelude.False)
                                     (bool_rec (\x2 ->
                                       case x2 of {
                                        Prelude.True -> Prelude.True;
                                        Prelude.False -> Prelude.False})
                                       (\x2 ->
                                       case x2 of {
                                        Prelude.True -> Prelude.False;
                                        Prelude.False -> Prelude.True}) b6
                                       b14)) (\_ -> Prelude.False)
                                   (bool_rec (\x2 ->
                                     case x2 of {
                                      Prelude.True -> Prelude.True;
                                      Prelude.False -> Prelude.False})
                                     (\x2 ->
                                     case x2 of {
                                      Prelude.True -> Prelude.False;
                                      Prelude.False -> Prelude.True}) b5 b13))
                                 (\_ -> Prelude.False)
                                 (bool_rec (\x2 ->
                                   case x2 of {
                                    Prelude.True -> Prelude.True;
                                    Prelude.False -> Prelude.False}) (\x2 ->
                                   case x2 of {
                                    Prelude.True -> Prelude.False;
                                    Prelude.False -> Prelude.True}) b4 b12))
                               (\_ -> Prelude.False)
                               (bool_rec (\x2 ->
                                 case x2 of {
                                  Prelude.True -> Prelude.True;
                                  Prelude.False -> Prelude.False}) (\x2 ->
                                 case x2 of {
                                  Prelude.True -> Prelude.False;
                                  Prelude.False -> Prelude.True}) b3 b11))
                             (\_ -> Prelude.False)
                             (bool_rec (\x2 ->
                               case x2 of {
                                Prelude.True -> Prelude.True;
                                Prelude.False -> Prelude.False}) (\x2 ->
                               case x2 of {
                                Prelude.True -> Prelude.False;
                                Prelude.False -> Prelude.True}) b2 b10))
                           (\_ -> Prelude.False)
                           (bool_rec (\x2 ->
                             case x2 of {
                              Prelude.True -> Prelude.True;
                              Prelude.False -> Prelude.False}) (\x2 ->
                             case x2 of {
                              Prelude.True -> Prelude.False;
                              Prelude.False -> Prelude.True}) b1 b9)) (\_ ->
                         Prelude.False)
                         (bool_rec (\x2 ->
                           case x2 of {
                            Prelude.True -> Prelude.True;
                            Prelude.False -> Prelude.False}) (\x2 ->
                           case x2 of {
                            Prelude.True -> Prelude.False;
                            Prelude.False -> Prelude.True}) b0 b8)) (\_ ->
                       Prelude.False)
                       (bool_rec (\x2 ->
                         case x2 of {
                          Prelude.True -> Prelude.True;
                          Prelude.False -> Prelude.False}) (\x2 ->
                         case x2 of {
                          Prelude.True -> Prelude.False;
                          Prelude.False -> Prelude.True}) b b7)}) a0 a1)}) p
             a}
      in
      case h of {
       Prelude.True -> Prelude.True;
       Prelude.False -> iHl}) l;
   Prelude.Nothing -> Prelude.False}

executable_dec :: Term -> Plc -> Environment -> Prelude.Bool
executable_dec t k0 e =
  term_rec (\a k1 -> hasASPe_dec k1 e a) (\p _ iHt k1 ->
    let {h = knowsOfe_dec k1 e p} in
    case h of {
     Prelude.True -> iHt p;
     Prelude.False -> Prelude.True}) (\_ iHt1 _ iHt2 k1 ->
    let {iHt3 = iHt1 k1} in
    let {iHt4 = iHt2 k1} in
    case iHt3 of {
     Prelude.True -> iHt4;
     Prelude.False -> Prelude.False}) (\_ _ iHt1 _ iHt2 k1 ->
    let {iHt3 = iHt1 k1} in
    let {iHt4 = iHt2 k1} in
    case iHt3 of {
     Prelude.True -> iHt4;
     Prelude.False -> Prelude.False}) (\_ _ iHt1 _ iHt2 k1 ->
    let {iHt3 = iHt1 k1} in
    let {iHt4 = iHt2 k1} in
    case iHt3 of {
     Prelude.True -> iHt4;
     Prelude.False -> Prelude.False}) t k0

checkTermPolicy_dec :: Term -> Plc -> Environment -> (Plc -> ASP ->
                       Prelude.Bool) -> Prelude.Bool
checkTermPolicy_dec t k0 _ h =
  term_rec (\a -> h k0 a) (\_ _ iHt -> iHt) (\_ iHt1 _ iHt2 ->
    case iHt1 of {
     Prelude.True -> iHt2;
     Prelude.False -> Prelude.False}) (\_ _ iHt1 _ iHt2 ->
    case iHt1 of {
     Prelude.True -> iHt2;
     Prelude.False -> Prelude.False}) (\_ _ iHt1 _ iHt2 ->
    case iHt1 of {
     Prelude.True -> iHt2;
     Prelude.False -> Prelude.False}) t

sound_dec :: Term -> Plc -> Environment -> (Plc -> ASP -> Prelude.Bool) ->
             Prelude.Bool
sound_dec t p e h =
  let {h0 = executable_dec t p e} in
  let {h1 = checkTermPolicy_dec t p e h} in
  case h0 of {
   Prelude.True -> h1;
   Prelude.False -> Prelude.False}

e_P0 :: String -> Prelude.Maybe Manifest
e_P0 =
  e_update e_empty (String0 (Ascii Prelude.False Prelude.False Prelude.False
    Prelude.False Prelude.True Prelude.False Prelude.True Prelude.False)
    (String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.True Prelude.False Prelude.False) EmptyString))
    (Prelude.Just (Build_Manifest ([]) ((:) (String0 (Ascii Prelude.False
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.False
    Prelude.True Prelude.False) (String0 (Ascii Prelude.True Prelude.False
    Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
    Prelude.False) EmptyString)) ([])) ([])))

e_P1 :: String -> Prelude.Maybe Manifest
e_P1 =
  e_update e_P0 (String0 (Ascii Prelude.False Prelude.False Prelude.False
    Prelude.False Prelude.True Prelude.False Prelude.True Prelude.False)
    (String0 (Ascii Prelude.True Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.True Prelude.False Prelude.False) EmptyString))
    (Prelude.Just (Build_Manifest ((:) (ASPC ALL EXTD (Asp_paramsC (String0
    (Ascii Prelude.True Prelude.False Prelude.False Prelude.False
    Prelude.False Prelude.True Prelude.True Prelude.False) (String0 (Ascii
    Prelude.False Prelude.True Prelude.True Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.True
    Prelude.True Prelude.False Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.False) EmptyString))) ((:) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.True Prelude.True Prelude.False) EmptyString) ([])) (String0
    (Ascii Prelude.False Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.False Prelude.True Prelude.False) (String0 (Ascii
    Prelude.True Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.False Prelude.False) EmptyString)) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.True
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.False Prelude.False) EmptyString)))) ((:) (ASPC ALL EXTD
    (Asp_paramsC (String0 (Ascii Prelude.True Prelude.False Prelude.False
    Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False)
    (String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.False Prelude.True Prelude.False) (String0 (Ascii
    Prelude.True Prelude.True Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.False
    Prelude.False Prelude.False Prelude.True Prelude.False Prelude.False
    Prelude.True Prelude.False) EmptyString)))) ((:) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.True Prelude.True Prelude.False) EmptyString) ([])) (String0
    (Ascii Prelude.False Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.False Prelude.True Prelude.False) (String0 (Ascii
    Prelude.True Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.False Prelude.False) EmptyString)) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.True
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.False Prelude.False) EmptyString)))) ([]))) ((:) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.False
    Prelude.True Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.False Prelude.False) EmptyString)) ([])) ([])))

e_P2 :: String -> Prelude.Maybe Manifest
e_P2 =
  e_update e_P1 (String0 (Ascii Prelude.False Prelude.False Prelude.False
    Prelude.False Prelude.True Prelude.False Prelude.True Prelude.False)
    (String0 (Ascii Prelude.False Prelude.True Prelude.False Prelude.False
    Prelude.True Prelude.True Prelude.False Prelude.False) EmptyString))
    (Prelude.Just (Build_Manifest ((:) (ASPC ALL EXTD (Asp_paramsC (String0
    (Ascii Prelude.True Prelude.False Prelude.False Prelude.False
    Prelude.False Prelude.True Prelude.True Prelude.False) (String0 (Ascii
    Prelude.True Prelude.True Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.False
    Prelude.True Prelude.True Prelude.False Prelude.False Prelude.False
    Prelude.True Prelude.False) (String0 (Ascii Prelude.True Prelude.True
    Prelude.False Prelude.False Prelude.True Prelude.False Prelude.True
    Prelude.False) EmptyString)))) ((:) (String0 (Ascii Prelude.False
    Prelude.False Prelude.False Prelude.True Prelude.True Prelude.True
    Prelude.True Prelude.False) EmptyString) ([])) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.False
    Prelude.True Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.False Prelude.False) EmptyString)) (String0 (Ascii Prelude.False
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.False
    Prelude.True Prelude.False) (String0 (Ascii Prelude.False Prelude.True
    Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
    Prelude.False) EmptyString)))) ([])) ([]) ((:) (String0 (Ascii
    Prelude.False Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.False Prelude.True Prelude.False) (String0 (Ascii Prelude.True
    Prelude.False Prelude.False Prelude.False Prelude.True Prelude.True
    Prelude.False Prelude.False) EmptyString)) ([]))))

string_dec0 :: String -> String -> Prelude.Bool
string_dec0 s s' =
  string_rec (\x ->
    case x of {
     EmptyString -> Prelude.True;
     String0 _ _ -> Prelude.False}) (\a _ x x0 ->
    case x0 of {
     EmptyString -> Prelude.False;
     String0 a0 s0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x s0)) (\_ ->
        Prelude.False)
        (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
          case x1 of {
           Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False)
                            (bool_rec (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.True;
                               Prelude.False -> Prelude.False}) (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.False;
                               Prelude.False -> Prelude.True}) b6 b14))
                          (\_ -> Prelude.False)
                          (bool_rec (\x2 ->
                            case x2 of {
                             Prelude.True -> Prelude.True;
                             Prelude.False -> Prelude.False}) (\x2 ->
                            case x2 of {
                             Prelude.True -> Prelude.False;
                             Prelude.False -> Prelude.True}) b5 b13)) (\_ ->
                        Prelude.False)
                        (bool_rec (\x2 ->
                          case x2 of {
                           Prelude.True -> Prelude.True;
                           Prelude.False -> Prelude.False}) (\x2 ->
                          case x2 of {
                           Prelude.True -> Prelude.False;
                           Prelude.False -> Prelude.True}) b4 b12)) (\_ ->
                      Prelude.False)
                      (bool_rec (\x2 ->
                        case x2 of {
                         Prelude.True -> Prelude.True;
                         Prelude.False -> Prelude.False}) (\x2 ->
                        case x2 of {
                         Prelude.True -> Prelude.False;
                         Prelude.False -> Prelude.True}) b3 b11)) (\_ ->
                    Prelude.False)
                    (bool_rec (\x2 ->
                      case x2 of {
                       Prelude.True -> Prelude.True;
                       Prelude.False -> Prelude.False}) (\x2 ->
                      case x2 of {
                       Prelude.True -> Prelude.False;
                       Prelude.False -> Prelude.True}) b2 b10)) (\_ ->
                  Prelude.False)
                  (bool_rec (\x2 ->
                    case x2 of {
                     Prelude.True -> Prelude.True;
                     Prelude.False -> Prelude.False}) (\x2 ->
                    case x2 of {
                     Prelude.True -> Prelude.False;
                     Prelude.False -> Prelude.True}) b1 b9)) (\_ ->
                Prelude.False)
                (bool_rec (\x2 ->
                  case x2 of {
                   Prelude.True -> Prelude.True;
                   Prelude.False -> Prelude.False}) (\x2 ->
                  case x2 of {
                   Prelude.True -> Prelude.False;
                   Prelude.False -> Prelude.True}) b0 b8)) (\_ ->
              Prelude.False)
              (bool_rec (\x2 ->
                case x2 of {
                 Prelude.True -> Prelude.True;
                 Prelude.False -> Prelude.False}) (\x2 ->
                case x2 of {
                 Prelude.True -> Prelude.False;
                 Prelude.False -> Prelude.True}) b b7)}) a a0)}) s s'

plc_dec :: Plc -> Plc -> Prelude.Bool
plc_dec =
  string_dec0

p0_Policy_dec :: ASP -> Plc -> Prelude.Bool
p0_Policy_dec _ _ =
  Prelude.False

p1_Policy_dec :: ASP -> Plc -> Prelude.Bool
p1_Policy_dec asp plc =
  case asp of {
   ASPC s f a ->
    let {
     h = aSP_dec (ASPC s f a) (ASPC ALL EXTD (Asp_paramsC (String0 (Ascii
           Prelude.True Prelude.False Prelude.False Prelude.False
           Prelude.False Prelude.True Prelude.True Prelude.False) (String0
           (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
           Prelude.False Prelude.False Prelude.True Prelude.False) (String0
           (Ascii Prelude.True Prelude.True Prelude.False Prelude.False
           Prelude.True Prelude.False Prelude.True Prelude.False) (String0
           (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
           Prelude.False Prelude.False Prelude.True Prelude.False)
           EmptyString)))) ((:) (String0 (Ascii Prelude.False Prelude.False
           Prelude.False Prelude.True Prelude.True Prelude.True Prelude.True
           Prelude.False) EmptyString) ([])) (String0 (Ascii Prelude.False
           Prelude.False Prelude.False Prelude.False Prelude.True
           Prelude.False Prelude.True Prelude.False) (String0 (Ascii
           Prelude.True Prelude.False Prelude.False Prelude.False
           Prelude.True Prelude.True Prelude.False Prelude.False)
           EmptyString)) (String0 (Ascii Prelude.False Prelude.False
           Prelude.False Prelude.False Prelude.True Prelude.False
           Prelude.True Prelude.False) (String0 (Ascii Prelude.True
           Prelude.False Prelude.False Prelude.False Prelude.True
           Prelude.True Prelude.False Prelude.False) EmptyString))))}
    in
    let {
     h0 = aSP_dec (ASPC s f a) (ASPC ALL EXTD (Asp_paramsC (String0 (Ascii
            Prelude.True Prelude.False Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.True Prelude.False) (String0
            (Ascii Prelude.False Prelude.True Prelude.True Prelude.False
            Prelude.True Prelude.False Prelude.True Prelude.False) (String0
            (Ascii Prelude.True Prelude.True Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False)
            EmptyString))) ((:) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.True Prelude.True Prelude.True
            Prelude.False) EmptyString) ([])) (String0 (Ascii Prelude.False
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.False Prelude.True Prelude.False) (String0 (Ascii
            Prelude.True Prelude.False Prelude.False Prelude.False
            Prelude.True Prelude.True Prelude.False Prelude.False)
            EmptyString)) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.True
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))))}
    in
    let {
     h1 = plc_dec plc (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.False
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))}
    in
    case h of {
     Prelude.True ->
      case h0 of {
       Prelude.True ->
        case h1 of {
         Prelude.True ->
          eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.False Prelude.True
            Prelude.False) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.True
            Prelude.False Prelude.False) EmptyString)) false_rec plc;
         Prelude.False -> false_rec};
       Prelude.False ->
        case h1 of {
         Prelude.True ->
          eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.False Prelude.True
            Prelude.False) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.True
            Prelude.False Prelude.False) EmptyString))
            (eq_rec_r (ASPC ALL EXTD (Asp_paramsC (String0 (Ascii
              Prelude.True Prelude.False Prelude.False Prelude.False
              Prelude.False Prelude.True Prelude.True Prelude.False) (String0
              (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
              Prelude.False Prelude.False Prelude.True Prelude.False)
              (String0 (Ascii Prelude.True Prelude.True Prelude.False
              Prelude.False Prelude.True Prelude.False Prelude.True
              Prelude.False) (String0 (Ascii Prelude.False Prelude.False
              Prelude.False Prelude.True Prelude.False Prelude.False
              Prelude.True Prelude.False) EmptyString)))) ((:) (String0
              (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
              Prelude.True Prelude.True Prelude.True Prelude.False)
              EmptyString) ([])) (String0 (Ascii Prelude.False Prelude.False
              Prelude.False Prelude.False Prelude.True Prelude.False
              Prelude.True Prelude.False) (String0 (Ascii Prelude.True
              Prelude.False Prelude.False Prelude.False Prelude.True
              Prelude.True Prelude.False Prelude.False) EmptyString))
              (String0 (Ascii Prelude.False Prelude.False Prelude.False
              Prelude.False Prelude.True Prelude.False Prelude.True
              Prelude.False) (String0 (Ascii Prelude.True Prelude.False
              Prelude.False Prelude.False Prelude.True Prelude.True
              Prelude.False Prelude.False) EmptyString)))) Prelude.True (ASPC
              s f a)) plc;
         Prelude.False -> Prelude.False}};
     Prelude.False ->
      case h0 of {
       Prelude.True ->
        case h1 of {
         Prelude.True ->
          eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.False Prelude.True
            Prelude.False) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.True
            Prelude.False Prelude.False) EmptyString))
            (eq_rec_r (ASPC ALL EXTD (Asp_paramsC (String0 (Ascii
              Prelude.True Prelude.False Prelude.False Prelude.False
              Prelude.False Prelude.True Prelude.True Prelude.False) (String0
              (Ascii Prelude.False Prelude.True Prelude.True Prelude.False
              Prelude.True Prelude.False Prelude.True Prelude.False) (String0
              (Ascii Prelude.True Prelude.True Prelude.False Prelude.False
              Prelude.False Prelude.False Prelude.True Prelude.False)
              EmptyString))) ((:) (String0 (Ascii Prelude.False Prelude.False
              Prelude.False Prelude.True Prelude.True Prelude.True
              Prelude.True Prelude.False) EmptyString) ([])) (String0 (Ascii
              Prelude.False Prelude.False Prelude.False Prelude.False
              Prelude.True Prelude.False Prelude.True Prelude.False) (String0
              (Ascii Prelude.True Prelude.False Prelude.False Prelude.False
              Prelude.True Prelude.True Prelude.False Prelude.False)
              EmptyString)) (String0 (Ascii Prelude.False Prelude.False
              Prelude.False Prelude.False Prelude.True Prelude.False
              Prelude.True Prelude.False) (String0 (Ascii Prelude.True
              Prelude.False Prelude.False Prelude.False Prelude.True
              Prelude.True Prelude.False Prelude.False) EmptyString))))
              Prelude.True (ASPC s f a)) plc;
         Prelude.False -> Prelude.False};
       Prelude.False ->
        case h1 of {
         Prelude.True ->
          eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
            Prelude.False Prelude.True Prelude.False Prelude.True
            Prelude.False) (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.True
            Prelude.False Prelude.False) EmptyString)) Prelude.False plc;
         Prelude.False -> Prelude.False}}};
   _ -> Prelude.False}

p2_Policy_dec :: ASP -> Plc -> Prelude.Bool
p2_Policy_dec asp plc =
  case asp of {
   ASPC s f a ->
    let {
     h = aSP_dec (ASPC s f a) (ASPC ALL EXTD (Asp_paramsC (String0 (Ascii
           Prelude.True Prelude.False Prelude.False Prelude.False
           Prelude.False Prelude.True Prelude.True Prelude.False) (String0
           (Ascii Prelude.True Prelude.True Prelude.False Prelude.False
           Prelude.True Prelude.False Prelude.True Prelude.False) (String0
           (Ascii Prelude.False Prelude.True Prelude.True Prelude.False
           Prelude.False Prelude.False Prelude.True Prelude.False) (String0
           (Ascii Prelude.True Prelude.True Prelude.False Prelude.False
           Prelude.True Prelude.False Prelude.True Prelude.False)
           EmptyString)))) ((:) (String0 (Ascii Prelude.False Prelude.False
           Prelude.False Prelude.True Prelude.True Prelude.True Prelude.True
           Prelude.False) EmptyString) ([])) (String0 (Ascii Prelude.False
           Prelude.False Prelude.False Prelude.False Prelude.True
           Prelude.False Prelude.True Prelude.False) (String0 (Ascii
           Prelude.False Prelude.True Prelude.False Prelude.False
           Prelude.True Prelude.True Prelude.False Prelude.False)
           EmptyString)) (String0 (Ascii Prelude.False Prelude.False
           Prelude.False Prelude.False Prelude.True Prelude.False
           Prelude.True Prelude.False) (String0 (Ascii Prelude.False
           Prelude.True Prelude.False Prelude.False Prelude.True Prelude.True
           Prelude.False Prelude.False) EmptyString))))}
    in
    let {
     h0 = plc_dec plc (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.True
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))}
    in
    case h of {
     Prelude.True -> h0;
     Prelude.False -> Prelude.False};
   _ -> Prelude.False}

sound_local_policies :: Plc -> ASP -> Prelude.Bool
sound_local_policies p a =
  let {
   h = plc_dec p (String0 (Ascii Prelude.False Prelude.False Prelude.False
         Prelude.False Prelude.True Prelude.False Prelude.True Prelude.False)
         (String0 (Ascii Prelude.False Prelude.False Prelude.False
         Prelude.False Prelude.True Prelude.True Prelude.False Prelude.False)
         EmptyString))}
  in
  let {
   h0 = plc_dec p (String0 (Ascii Prelude.False Prelude.False Prelude.False
          Prelude.False Prelude.True Prelude.False Prelude.True
          Prelude.False) (String0 (Ascii Prelude.True Prelude.False
          Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
          Prelude.False) EmptyString))}
  in
  let {
   h1 = plc_dec p (String0 (Ascii Prelude.False Prelude.False Prelude.False
          Prelude.False Prelude.True Prelude.False Prelude.True
          Prelude.False) (String0 (Ascii Prelude.False Prelude.True
          Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
          Prelude.False) EmptyString))}
  in
  case h of {
   Prelude.True ->
    case h0 of {
     Prelude.True -> false_rec;
     Prelude.False ->
      case h1 of {
       Prelude.True -> false_rec;
       Prelude.False ->
        eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
          Prelude.False Prelude.True Prelude.False Prelude.True
          Prelude.False) (String0 (Ascii Prelude.False Prelude.False
          Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
          Prelude.False) EmptyString))
          (p0_Policy_dec a (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.False
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))) p}};
   Prelude.False ->
    case h0 of {
     Prelude.True ->
      case h1 of {
       Prelude.True -> false_rec;
       Prelude.False ->
        eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
          Prelude.False Prelude.True Prelude.False Prelude.True
          Prelude.False) (String0 (Ascii Prelude.True Prelude.False
          Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
          Prelude.False) EmptyString))
          (p1_Policy_dec a (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.True
            Prelude.False Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))) p};
     Prelude.False ->
      case h1 of {
       Prelude.True ->
        eq_rec_r (String0 (Ascii Prelude.False Prelude.False Prelude.False
          Prelude.False Prelude.True Prelude.False Prelude.True
          Prelude.False) (String0 (Ascii Prelude.False Prelude.True
          Prelude.False Prelude.False Prelude.True Prelude.True Prelude.False
          Prelude.False) EmptyString))
          (p2_Policy_dec a (String0 (Ascii Prelude.False Prelude.False
            Prelude.False Prelude.False Prelude.True Prelude.False
            Prelude.True Prelude.False) (String0 (Ascii Prelude.False
            Prelude.True Prelude.False Prelude.False Prelude.True
            Prelude.True Prelude.False Prelude.False) EmptyString))) p;
       Prelude.False -> Prelude.False}}}

sound_system_dec :: Term -> Plc -> Prelude.Bool
sound_system_dec t p =
  sound_dec t p e_P2 sound_local_policies

