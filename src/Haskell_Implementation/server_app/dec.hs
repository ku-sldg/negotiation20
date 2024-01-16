module Dec where

import Copland

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