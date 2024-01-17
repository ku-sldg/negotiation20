module Main where

import Copland
import Manifest
import System_spec
import Executable
import Policy

-- Print the result based on the Boolean value
printExecResult :: Bool -> Term -> IO ()
printExecResult True term = putStrLn $ "Term: " ++ show term ++ " is executable on the target system"
printExecResult False term = putStrLn $ "Term: " ++ show term ++ " is not executable"

printPolicyResult :: Bool -> Term -> IO ()
printPolicyResult True term = putStrLn $ "Term: " ++ show term ++ " satisfies Policy"
printPolicyResult False term = putStrLn $ "Term: " ++ show term ++ " does not satisfy policy"

main :: IO ()
main = do

    putStrLn "Initial Environment:"
    print targ_env

    let term1 = Coq_att 1 (Coq_asp aVC)

    -- check that hash is executable in place 1
    let isExec = (executable term1 0 targ_env)
    let isPol = (checkPolicy term1 0 1 targ_env)
    printExecResult isExec term1
    printPolicyResult isPol term1

    let term2 = (Coq_att 2 (Coq_asp aSFS))

    -- check that sfs is executable in place 2
    let isExec = (executable term2 1 targ_env)
    let isPol = (checkPolicy term2 1 2 targ_env)
    printExecResult isExec term2
    printPolicyResult isPol term2

    let term3 = Coq_lseq term1 term2

    -- check that sfs is executable in place 2
    let isExec = (executable term3 0 targ_env)
    let isPol = (checkPolicy term3 0 1 targ_env)
    printExecResult isExec term3
    printPolicyResult isPol term3