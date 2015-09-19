module ND where

open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Nullary

_⊢_ : Set → Set → Set
A ⊢ B = A → B

infix 3 _⊢_

_∧_ : Set → Set → Set
A ∧ B = A × B

∧I : {A B : Set} → A → B ⊢ A ∧ B
∧I A B = A , B

∧Eₗ : {A B : Set} → A ∧ B ⊢ A
∧Eₗ AB = proj₁ AB

∧Eᵣ : {A B : Set} → A ∧ B ⊢ B
∧Eᵣ AB = proj₂ AB

_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

∨Iₗ : {A B : Set} → A ⊢ A ∨ B
∨Iₗ A = inj₁ A

∨Iᵣ : {A B : Set} → B ⊢ A ∨ B
∨Iᵣ B = inj₂ B

∨E : {Γ A B C : Set} → Γ ⊢ A ∨ B → A ⊢ C → B ⊢ C → Γ ⊢ C
∨E x y z w with x w
... | inj₁ a = y a
... | inj₂ b = z b

¬I : {A B C : Set} → (A → B ⊢ C) → (A → B ⊢ ¬ C) → A ⊢ ¬ B
¬I x y z w = y z w (x z w)

postulate ¬E : {A B C : Set} → (A → ¬ B ⊢ C) → (A → ¬ B ⊢ ¬ C) → A ⊢ B

lem : ∀ {A : Set} → A ∨ (¬ A)
lem = {!!}

peirce : ∀ {A B : Set} → ((A → B) → A) → A
peirce x = x (λ a → {!!})
