module Main where

import Copland
import Manifest
import Executable

--  Build_Manifest (([]) ASP) (([]) Plc)
e_P0 :: Manifest
e_P0 = Build_Manifest ([]) ([1])

e_P1 :: Manifest
e_P1 = Build_Manifest ([(ASPC ("vc")), HSH]) ([2])

e_P2 :: Manifest
e_P2 = Build_Manifest ([(ASPC ("SFS"))]) ([1])

-- Print the result based on the Boolean value
printResult :: Bool -> Term -> IO ()
printResult True term = putStrLn $ "Term: " ++ show term ++ " is executable on the target system"
printResult False _ = putStrLn "Term is not executable"

main :: IO ()
main = do
    let targ_env = [(0, e_P0), (1, e_P1), (2, e_P2)]

    putStrLn "Initial Dictionary:"
    print targ_env

    let manifestValue = lookupByInt 2 targ_env
    putStrLn $ "Manifest for key 2: " ++ show manifestValue

    -- check that hash is executable in place 1
    let term1 = Coq_asp HSH
    let result = executable term1 1 targ_env
    printResult result term1

    -- let updatedDict = insertManifest 4 "ManifestD" myDict
    -- putStrLn "Updated Dictionary:"
    -- print updatedDict