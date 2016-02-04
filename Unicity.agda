module Unicity where

open import Data.Nat
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

uniq-ℕ : (n : ℕ) → n ≡ 0 ⊎ Σ[ m ∈ ℕ ] n ≡ (suc m)
uniq-ℕ zero = inj₁ refl
uniq-ℕ (suc n) = inj₂ (n , refl)

uniq-≡ : {A : Set} {a : A} → (e : Σ[ x ∈ A ] a ≡ x) → e ≡ (a , refl)
uniq-≡ (a , refl) = refl

uniq-Vec : {A : Set} → (e : Σ[ n ∈ ℕ ] Vec A n)
         → e ≡ (0 , []) ⊎ Σ[ m ∈ ℕ ] Σ[ x ∈ A ] Σ[ xs ∈ Vec A m ] e ≡ (suc m , x ∷ xs)
uniq-Vec (zero , []) = inj₁ refl
uniq-Vec (suc n , x ∷ xs) = inj₂ (n , x , xs , refl)
