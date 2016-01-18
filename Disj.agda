{-# OPTIONS --without-K #-}

module Disj where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

C : ℕ → Set
C zero = ⊤
C (suc n) = ⊥

0≢1 : 0 ≡ 1 → ⊥
0≢1 = λ ()

n≢0 : ∀ n → (suc n) ≡ 0 → ⊥
n≢0 n = λ ()

0≠1 : 0 ≡ 1 → ⊥
0≠1 f = subst C f tt

0≠n : ∀ n → 0 ≡ suc n → ⊥
0≠n zero = 0≠1
0≠n (suc n) f = 0≠n n (cong pred f)
