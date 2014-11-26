module Div where

open import Data.Nat

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

record ⊤ : Set where

data ⊥ : Set where

even : ℕ → Set
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

div2e : (n : ℕ) → even n → ℕ
div2e zero p = zero
div2e (suc zero) ()
div2e (suc (suc n)) p = suc (div2e n p)

data Even : ℕ → Set where
  ezero : Even zero
  esuc  : {n : ℕ} → Even n → Even (suc (suc n))

div2E : (n : ℕ) → Even n → ℕ
div2E zero ezero = zero
div2E (suc (suc n)) (esuc x) = suc (div2E n x)
