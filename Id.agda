module Id where

open import Level
open import Relation.Binary.PropositionalEquality

id : {A : Set} → A → A
id a = a

id-id-is-id : {A : Set} {a : A} → id (id a) ≡ id a
id-id-is-id = refl

id-id-id-is-id-id : {A : Set} {a : A} → id (id (id a)) ≡ id (id a)
id-id-id-is-id-id = refl

postulate _>>=_ : {A B : Set} {M : Set → Set} → M A → (A → M B) → M B

{-# NON_TERMINATING #-}
forever : {A B : Set} {M : Set → Set} → M A → M B → M B
forever {A} {B} {M} ma mb = _>>=_ {A} {B} {M} ma (λ a → forever {A} {B} {M} ma mb)
