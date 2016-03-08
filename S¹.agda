{-# OPTIONS --without-K #-}

module _ where

open import Relation.Binary.PropositionalEquality

transport = subst

module S¹ where

  private
    data S¹ : Set where
      base : S¹

  postulate
    loop : base ≡ base

  recS¹ : ∀ {ℓ} (C : Set ℓ)
        → (cbase : C)
        → (cloop : cbase ≡ cbase)
        → S¹ → C
  recS¹ C cbase cloop base = cbase

  indS¹ : ∀ {ℓ} (C : S¹ → Set ℓ)
        → (cbase : C base)
        → (cloop : cbase ≡ cbase)
        → (s : S¹) → C s
  indS¹ C cbase cloop base = cbase

  indS¹' : ∀ {ℓ} (C : S¹ → Set ℓ)
         → (cbase : C base)
         → (cloop : transport C loop cbase ≡ cbase)
         → (s : S¹) → C s
  indS¹' C cbase cloop p = indS¹ C cbase refl p
