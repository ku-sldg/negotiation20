module Example_sys_1 where

import qualified Prelude
import Copland
import Manifest

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

example_sys_1 :: ([]) (String -> Prelude.Maybe Manifest)
example_sys_1 =
  (:) e_P0 ((:) e_P1 ((:) e_P2 ([])))

