module Props where

data _∧_ (P : Set) (Q : Set) : Set where
   ∧-intro : P → Q → (P ∧ Q)

_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)

∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm′ (∧-intro p q) = ∧-intro q p

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm {P} {Q} = ∧-intro (∧-comm′ {P} {Q}) (∧-comm′ {Q} {P})

∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂
