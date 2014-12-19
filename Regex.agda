module Regex where

data Regex : Set where
  ε   : Regex
  _*  : Regex
  _+_ : Regex -> Regex -> Regex
  _∘_ : Regex -> Regex -> Regex
