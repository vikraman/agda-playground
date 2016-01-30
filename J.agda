module J where

postulate _≡_ : {A : Set} → A → A → Set
          refl : {A : Set} {x : A} → x ≡ x

J₁ : Set₁
J₁ = {A : Set} (P : (x y : A) → x ≡ y → Set)
   → ((x : A) → P x x refl)
   → (x y : A) (p : x ≡ y) → P x y p

J₂ : Set₁
J₂ = {A : Set} (x : A) (P : (y : A) → x ≡ y → Set)
   → P x refl
   → (y : A) (p : x ≡ y) → P y p

j₁₂ : J₁ → J₂
j₁₂ J = λ x P b y p → J (λ x y p → {!!}) (λ x → {!!}) x y p

j₂₁ : J₂ → J₁
j₂₁ J = λ P b x y p → J x (P x) (b x) y p
