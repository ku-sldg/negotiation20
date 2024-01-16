module Main where

import Copland
import Manifest
import System_spec
import Executable
import Policy

-- Print the result based on the Boolean value
printResult :: Bool -> Term -> IO ()
printResult True term = putStrLn $ "Term: " ++ show term ++ " is executable on the target system"
printResult False _ = putStrLn "Term is not executable"

main :: IO ()
main = do

    putStrLn "Initial Environment:"
    print targ_env

    -- check that hash is executable in place 1
    let isSound = (executable (Coq_asp HSH) 1 targ_env && checkPolicy (Coq_asp HSH) 1 targ_env)
    printResult isSound (Coq_asp HSH)

    -- let updatedDict = insertManifest 4 "ManifestD" myDict
    -- putStrLn "Updated Dictionary:"
    -- print updatedDict