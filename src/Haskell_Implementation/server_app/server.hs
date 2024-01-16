module Main where

import Manifest
import Copland

--  Build_Manifest (([]) ASP) (([]) Plc)
e_P0 :: Manifest
e_P0 = Build_Manifest ([]) ([1])

e_P1 :: Manifest
e_P1 = Build_Manifest ([(ASPC (Coq_asp_paramsC 1 (["vc"]) 1 1)), HSH]) ([2])

e_P2 :: Manifest
e_P2 = Build_Manifest ([(ASPC (Coq_asp_paramsC 2 (["SFS"]) 2 2))]) ([1])


main :: IO ()
main = do
    let myDict = [(0, e_P0), (1, e_P1), (2, e_P2)]

    putStrLn "Initial Dictionary:"
    print myDict

    let manifestValue = lookupByInt 2 myDict
    putStrLn $ "Manifest for key 2: " ++ show manifestValue

    --let updatedDict = insertManifest 4 "ManifestD" myDict
    --putStrLn "Updated Dictionary:"
    -- print updatedDict