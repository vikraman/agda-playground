module List where

open import Data.Nat

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

ns : List ℕ
ns = zero :: (suc zero :: (suc (suc zero) :: []))

[_] : {A : Set} → A → List A
[ a ] = a :: []

ms : List ℕ
ms = [ zero ]
