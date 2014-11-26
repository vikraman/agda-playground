module Dec where

open import Data.Nat

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

absurd : {P : Set} → ⊥ → P
absurd ()

infixr 9 ¬_

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no : (p : ¬ P) → Dec P

DecP : (P : ℕ → Set) → Set
DecP P = ∀ (n : ℕ) → Dec (P n)

neg : {P : Set} → Dec P → Dec (¬ P)
neg (yes p) = no (λ f → f p)
neg (no p) = yes p

neg' : {P : Set} → Dec (¬ P) → Dec P
neg' (yes p) = no p
neg' (no p) = yes {!!}

bar : {P Q : Set} → Dec P → (P → Q) → (¬ P → Q) → Q
bar (yes p) f g = f p
bar (no p) f g = g p

dneg : {P : Set} → Dec (¬ ¬ P) → Dec P
dneg (yes p) = yes {!!}
dneg (no p) = no (λ z → p (λ z₁ → z₁ z))

foo : {P : Set} → Dec (¬ P) → P → ⊥
foo (yes p) x = p x
foo (no p) x = {!!}
