module Hello where

data Unit : Set where
     unit : Unit
{-# COMPILED_DATA Unit () () #-}

postulate IO : Set -> Set
{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

open import Data.String

postulate putStrLn : String -> IO Unit
{-# COMPILED putStrLn putStrLn #-}

main : IO Unit
main = putStrLn "Hello World!"
