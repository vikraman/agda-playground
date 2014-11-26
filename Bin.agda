module Bin where

open import Data.Nat
open import Data.Nat.Properties

open import Function
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning

data Bin : Set where
  Z  : Bin
  E  : Bin → Bin
  SE : Bin → Bin

infixl 6 _++

_++ : Bin → Bin
Z ++ = SE Z
E n ++ = SE n
SE n ++ = E (n ++)

infixl 7 _⊞_

_⊞_ : Bin → Bin → Bin
Z ⊞ n = n
m ⊞ Z = m
E m ⊞ E n = E (m ⊞ n)
E m ⊞ SE n = (E (m ⊞ n)) ++
SE m ⊞ E n = E (m ⊞ n) ++
SE m ⊞ SE n = E ((m ⊞ n) ++)

⊞-right-identity : ∀ (n : Bin) → n ⊞ Z ≡ n
⊞-right-identity Z = refl
⊞-right-identity (E n) = refl
⊞-right-identity (SE n) = refl

⊞-comm : ∀ (m n : Bin) → m ⊞ n ≡ n ⊞ m
⊞-comm Z Z = refl
⊞-comm Z (E n) = refl
⊞-comm Z (SE n) = refl
⊞-comm (E m) Z = refl
⊞-comm (E m) (E n) = sym (cong E (⊞-comm n m))
⊞-comm (E m) (SE n) = sym (cong SE (⊞-comm n m))
⊞-comm (SE m) Z = refl
⊞-comm (SE m) (E n) = sym (cong SE (⊞-comm n m))
⊞-comm (SE m) (SE n) = cong (λ z → E (z ++)) (⊞-comm m n)

twice_ : ℕ → ℕ
twice zero = zero
twice suc n = suc (suc (twice n))

binToNat : Bin → ℕ
binToNat Z = 0
binToNat (E n) = twice (binToNat n)
binToNat (SE n) = suc (twice (binToNat n))

lemma : ∀ (n : Bin) → binToNat (n ++) ≡ suc (binToNat n)
lemma Z = refl
lemma (E _) = refl
lemma (SE n') =
  begin
    binToNat (SE n' ++)
  ≡⟨ refl ⟩
    binToNat (E (n' ++))
  ≡⟨ refl ⟩
    twice (binToNat (n' ++))
  ≡⟨ cong twice_ (lemma n') ⟩
    suc (suc (twice binToNat n'))
  ≡⟨ refl ⟩
    suc (suc (twice binToNat n'))
  ≡⟨ refl ⟩
    suc (binToNat (SE n'))
  ∎
