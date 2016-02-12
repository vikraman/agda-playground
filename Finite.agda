module _ where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Universe
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Function.Related.TypeIsomorphisms
open import Algebra

data U : Set where
  ZERO ONE   : U
  PLUS TIMES : U → U → U

⟦_⟧ : U → Set
⟦ ZERO ⟧ = ⊥
⟦ ONE ⟧ = ⊤
⟦ PLUS t₁ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

U-univ : Universe _ _
U-univ = record { U = U ; El = ⟦_⟧ }

_⟶_ : ∀ A B → Set
A ⟶ B = ⟦ A ⟧ → ⟦ B ⟧

data _⟷_ : U → U → Set where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} →
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} →
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

data _≡ᵤ_ (A : U) : U → Set where
  iso : {B : U} → A ⟷ B → A ≡ᵤ B

record _≃_ (A B : U) : Set where
  field
    f : A ⟶ B
    g : B ⟶ A
    f-g : ∀ x → f (g x) ≡ x
    g-f : ∀ x → g (f x) ≡ x

≡ᵤ-is-≃ : ∀ {A B} → A ≡ᵤ B → A ≃ B
≡ᵤ-is-≃ (iso unite₊l) = {!!}
≡ᵤ-is-≃ (iso uniti₊l) = {!!}
≡ᵤ-is-≃ (iso unite₊r) = {!!}
≡ᵤ-is-≃ (iso uniti₊r) = {!!}
≡ᵤ-is-≃ (iso swap₊) = {!!}
≡ᵤ-is-≃ (iso assocl₊) = {!!}
≡ᵤ-is-≃ (iso assocr₊) = {!!}
≡ᵤ-is-≃ (iso unite⋆l) = {!!}
≡ᵤ-is-≃ (iso uniti⋆l) = {!!}
≡ᵤ-is-≃ (iso unite⋆r) = {!!}
≡ᵤ-is-≃ (iso uniti⋆r) = {!!}
≡ᵤ-is-≃ (iso swap⋆) = {!!}
≡ᵤ-is-≃ (iso assocl⋆) = {!!}
≡ᵤ-is-≃ (iso assocr⋆) = {!!}
≡ᵤ-is-≃ (iso absorbr) = {!!}
≡ᵤ-is-≃ (iso absorbl) = {!!}
≡ᵤ-is-≃ (iso factorzr) = {!!}
≡ᵤ-is-≃ (iso factorzl) = {!!}
≡ᵤ-is-≃ (iso dist) = {!!}
≡ᵤ-is-≃ (iso factor) = {!!}
≡ᵤ-is-≃ (iso distl) = {!!}
≡ᵤ-is-≃ (iso factorl) = {!!}
≡ᵤ-is-≃ (iso id⟷) = {!!}
≡ᵤ-is-≃ (iso (x ◎ x₁)) = {!!}
≡ᵤ-is-≃ (iso (x ⊕ x₁)) = {!!}
≡ᵤ-is-≃ (iso (x ⊗ x₁)) = {!!}

≃-is-≡ᵤ : ∀ {A B} → A ≃ B → A ≡ᵤ B
≃-is-≡ᵤ p = {!!}

private

  reflect : ∀ {A B} → A ≡ B → A ≃ B
  reflect refl = record { f = id ; g = id ; f-g = λ x → refl ; g-f = λ x → refl }

  ≃-equiv : IsEquivalence _≃_
  ≃-equiv = record { refl = reflect refl
                   ; sym = λ x → record { f = g x ; g = f x
                                        ; f-g = g-f x ; g-f = f-g x
                                        }
                   ; trans = λ x y → record { f = f y ∘ f x
                                            ; g = g x ∘ g y
                                            ; f-g = λ z → {!!}
                                            ; g-f = λ z → {!!}
                                            }
                   }
          where open _≃_

U-setoid : Setoid _ _
U-setoid = record { Carrier = U
                  ; _≈_ = _≃_
                  ; isEquivalence = ≃-equiv
                  }

open Setoid U-setoid
