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

K : ∀ {ℓ} {A : Set ℓ} {a : A}
  → (C : a ≡ a → Set ℓ)
  → C refl → (p : a ≡ a) -> C p
K C c refl = c

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

C : Bool ≡ Bool → Set₁
C p = p ≡ refl

C₁ : p₁ ≡ refl
C₁ = K C refl p₁

C₂ : p₂ ≡ refl
C₂ = K C refl p₂

p≡ : (p₁ : Bool ≡ Bool) → (p₂ : Bool ≡ Bool) → p₁ ≡ p₂
p≡ p₁ p₂ = {!!} -- trans C₁ (sym C₂)

p₁₂ : p₁ ≡ p₂
p₁₂ = p≡ p₁ p₂
