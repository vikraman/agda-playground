module Barendregt where

module Star where
  data ⊥ : Set₁ where

  ¬ : Set → Set₁
  ¬ a = a → ⊥

  term : {A B : Set} → A → B → ¬ A → ¬ B
  term a b ¬a p = ¬a a

module NotStar where
  data ⊥ : Set where

  ¬ : Set → Set
  ¬ a = a → ⊥

  term : {A B : Set} → A → B → ¬ A → ¬ B
  term a _ ¬a _ = ¬a a
