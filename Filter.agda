module Filter where

-- open import Size
-- open import Data.Bool
-- open import Data.List

-- filterN : {A : Set} {n : Size} → (A → Bool) → List A → List A
-- filterN p [] = []
-- filterN p (a ∷ as) with p a
-- filterN p (a ∷ as) | true with as
-- filterN p (a ∷ as) | true | [] = a ∷ []
-- filterN p (a ∷ as) | true | b ∷ bs with p b
-- filterN p (a ∷ as) | true | b ∷ bs | true = a ∷ (b ∷ filterN p bs)
-- filterN p (a ∷ as) | true | b ∷ bs | false = a ∷ filterN p bs
-- filterN p (a ∷ as) | false = filterN p as

-- -- filterN p [] = []
-- -- filterN p (a ∷ as) with p a
-- -- filterN p (a ∷ as) | true = a ∷ filterN p as
-- -- filterN p (a ∷ as) | false = filterN p as

-- module filter where
-- data Bool : Set where
--   true false : Bool

-- data List (A : Set) : Set where
--   []  : List A
--   _::_ : A → List A → List A

data Bool : Set where
  true false : Bool

data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A

open import Relation.Binary.PropositionalEquality

lemma : {A : Set} {a : A} {x y : List A} → x ≡ y → a :: x ≡ a :: y
lemma p rewrite p = refl

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (a :: as) with p a
... | true  = a :: (filter p as)
... | false = filter p as

filterfilter : {A : Set} → (p : A → Bool) → (as : List A) → filter p (filter p as) ≡ filter p as
filterfilter p [] = refl
filterfilter p (a :: as) rewrite (filterfilter p as) with p a
filterfilter p (a :: as) | true = {!c!}
filterfilter p (a :: as) | false = filterfilter p as

filterP : {A : Set} → (A → Bool) → List A → List A
filterP p [] = []
filterP p (a :: []) with p a
filterP p (a :: []) | true = a :: []
filterP p (a :: []) | false = []
filterP p (a :: (b :: bs)) with p a | p b
filterP p (a :: (b :: bs)) | true | true = a :: (b :: filterP p bs)
filterP p (a :: (b :: bs)) | true | false = a :: filterP p bs
filterP p (a :: (b :: bs)) | false | true = b :: filter p bs
filterP p (a :: (b :: bs)) | false | false = filterP p bs

filter≡filterP₀ : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterP p as
filter≡filterP₀ p [] = refl
filter≡filterP₀ p (a :: []) with p a
filter≡filterP₀ p (a :: []) | true = refl
filter≡filterP₀ p (a :: []) | false = refl
filter≡filterP₀ p (a :: (b :: bs)) with p a
filter≡filterP₀ p (a :: (b :: bs)) | true with p b
filter≡filterP₀ p (a :: (b :: bs)) | true | true rewrite (filter≡filterP₀ p bs) = refl
filter≡filterP₀ p (a :: (b :: bs)) | true | false rewrite (filter≡filterP₀ p bs) = refl
filter≡filterP₀ p (a :: (b :: bs)) | false with p b
filter≡filterP₀ p (a :: (b :: bs)) | false | true rewrite (filter≡filterP₀ p bs) = refl
filter≡filterP₀ p (a :: (b :: bs)) | false | false rewrite (filter≡filterP₀ p bs) = refl

filter≡filterP : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterP p as
filter≡filterP p [] = refl
filter≡filterP p (a :: []) with p a
filter≡filterP p (a :: []) | true = refl
filter≡filterP p (a :: []) | false = refl
filter≡filterP p (a :: (b :: bs)) with p a
filter≡filterP p (a :: (b :: bs)) | true with p b
filter≡filterP p (a :: (b :: bs)) | true | true = cong (λ x → a :: (b :: x)) (filter≡filterP p bs)
filter≡filterP p (a :: (b :: bs)) | true | false = cong (λ x → a :: x) (filter≡filterP p bs)
filter≡filterP p (a :: (b :: bs)) | false with p b
filter≡filterP p (a :: (b :: bs)) | false | true = cong (λ x → b :: x) refl
filter≡filterP p (a :: (b :: bs)) | false | false = filter≡filterP p bs

{-# NON_TERMINATING #-}
filterN : {A : Set} → (A → Bool) → List A → List A
filterN p [] = []
filterN p (a :: as) with p a
filterN p (a :: as) | true  with as
filterN p (a :: as) | true | [] = a :: []
filterN p (a :: as) | true | b :: bs with p b
filterN p (a :: as) | true | b :: bs | true  = a :: (b :: filterN p bs)
filterN p (a :: as) | true | b :: bs | false = a :: filterN p bs
filterN p (a :: as) | false = filterN p as

filter≡filterN : {A : Set} → (p : A → Bool) → (as : List A) → filterN p as ≡ filter p as
filter≡filterN p [] = {!!}
filter≡filterN p (a :: as) with p a
filter≡filterN p (a :: as) | true with as
filter≡filterN p (a :: as) | true | [] = {!!}
filter≡filterN p (a :: as) | true | b :: bs with p b
filter≡filterN p (a :: as) | true | b :: bs | true = {!!}
filter≡filterN p (a :: as) | true | b :: bs | false = {!!}
filter≡filterN p (a :: as) | false = {!!}
