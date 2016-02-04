module BoolIso where

open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality

record _≈_ (A B : Set) : Set where
  field
    f : A → B
    g : B → A
    .l : ∀ {x} → f (g x) ≡ x
    .r : ∀ {x} → g (f x) ≡ x

postulate
  ua : {A B : Set} → A ≈ B → A ≡ B

p₁ : Bool ≡ Bool
p₁ = ua record { f = id
               ; g = id
               ; l = refl
               ; r = refl
               }

p₂ : Bool ≡ Bool
p₂ = ua record { f = not
               ; g = not
               ; l = λ { {true} → refl ; {false} → refl }
               ; r = λ { {true} → refl ; {false} → refl }
               }

p₁₂ : p₁ ≡ p₂
p₁₂ = {!!}
