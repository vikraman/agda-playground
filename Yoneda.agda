{-# OPTIONS --type-in-type #-}

module Yoneda where

_∘_ : {a b c : Set} → (b → c) → (a → b) → (a → c)
f ∘ g = λ z → f (g z)

record Functor (f : Set → Set) : Set where
  field
    map : {a b : Set} → (a → b) → f a → f b

Yoneda : (f : Set → Set) → (a : Set) → Set
Yoneda f a = {b : Set} → (a → b) → f b

YonedaFunctor : ∀ {f : Set → Set} → Functor (Yoneda f)
YonedaFunctor = record { map = λ f y → λ k → y (k ∘ f) }

data CoYoneda (f : Set → Set) (a : Set) : Set where
     coyo : {b : Set} → (b → a) → f b → CoYoneda f a

CoYonedaFunctor : ∀ {f : Set → Set} → Functor (CoYoneda f)
CoYonedaFunctor = record { map = λ { f (coyo g v) → coyo (f ∘ g) v } }

open import Data.Product
