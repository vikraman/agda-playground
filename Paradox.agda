module Paradox where

open import Coinduction
open import Relation.Binary.PropositionalEquality

data False : Set where

data CoFalse : Set where
   CF : False → CoFalse

data Pandora : Set where
   C : ∞ CoFalse → Pandora

postulate
   ext : (CoFalse → Pandora) → (Pandora → CoFalse) → CoFalse ≡ Pandora

out : CoFalse → False
out (CF f) = f

foo : CoFalse ≡ Pandora
foo = ext (λ { (CF ()) })
          (λ { (C c) → CF (out (♭ c)) })

loop : CoFalse
loop rewrite foo = C (♯ loop)

false : False
false = out loop
