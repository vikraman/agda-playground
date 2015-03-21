module Eq where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  trans : {y z : A} → x ≡ y → y ≡ z → x ≡ z

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
sym (trans a≡c c≡b) = trans (sym c≡b) (sym a≡c)

trans' : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' refl p' = p'
trans' (trans p p'') p' = trans (trans' p p'') p'

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl
cong f (trans p p') = trans (cong f p) (cong f p')

subst : {A : Set} {a b : A} → (f : A → Set) → a ≡ b → f a → f b
subst f refl x = x
subst f (trans p p') x = subst f p' (subst f p x)
