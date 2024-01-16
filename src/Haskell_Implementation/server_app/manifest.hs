module Manifest where

import Prelude
import Copland

-- Manifest includes list of ASPs and the KnowsOf Relation
data Manifest = Build_Manifest [ASP] [Plc] 

instance Show Manifest where
    show (Build_Manifest asps plcs) =
        "Build_Manifest " ++ show asps ++ " " ++ show plcs

type Environment = [(Int, Manifest)]

-- Function to find a manifest by key in the dictionary
lookupByInt :: Int -> Environment -> Maybe Manifest
lookupByInt _ [] = Nothing
lookupByInt key ((k, v):dict)
  | key == k  = Just v
  | otherwise = lookupByInt key dict

-- Function to insert a key-manifest pair into the dictionary
insertManifest :: Int -> Manifest -> Environment -> Environment
insertManifest key manifest dict = (key, manifest) : dict
