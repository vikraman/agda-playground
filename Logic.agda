module Logic where

record ⊤ : Set where

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

data _∧_ (A B : Set) : Set where
  ⟨_,_⟩ : (a : A) → (b : B) → A ∧ B

data _∨_ (A B : Set) : Set where
  inl : (a : A) → A ∨ B
  inr : (b : B) → A ∨ B

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

infixr 1 _∧_
infixr 1 _∨_
infixr 0 _↔_
infix  2 ¬_

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

doubleNegation : {A : Set} → A → ¬ ¬ A
doubleNegation a neg = neg a

deMorgan1 : {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
deMorgan1 notAorB = ⟨ notAorB ∘ inl , notAorB ∘ inr ⟩

deMorgan2 : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
deMorgan2 ⟨ notA , notB ⟩ (inl a) = notA a
deMorgan2 ⟨ notA , notB ⟩ (inr b) = notB b

deMorgan : {A B : Set} → ¬ (A ∨ B) ↔ ¬ A ∧ ¬ B
deMorgan = ⟨ deMorgan1 , deMorgan2 ⟩

prop₁ : {P : Set} → ¬(¬(P ∨ ¬ P))
prop₁ f = f (inr (λ x → f (inl x)))
