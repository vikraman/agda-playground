module Greater where

data ℕ : Set where
  ℤ : ℕ
  Suc : ℕ → ℕ

data _≤_ : (x y : ℕ) → Set where
  z : ∀ {n : ℕ} → ℤ ≤ n
  s : ∀ {n m : ℕ} → n ≤ m → Suc n ≤ Suc m

two : ℕ
two = Suc (Suc ℤ)

three : ℕ
three = Suc (Suc (Suc ℤ))

two≤three : two ≤ three
two≤three = s (s z)

trans : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans z b = z
trans (s a) (s b) = s (trans a b)

trans' : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans' z z = z
trans' z (s b) = z
trans' (s a) (s b) = s (trans' a b)
