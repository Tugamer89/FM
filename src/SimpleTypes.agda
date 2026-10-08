module SimpleTypes where

  data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B

  pr₁ : {A B : Set} → A ∧ B → A
  pr₁ (x , y) = x

  pr₂ : {A B : Set} → A ∧ B → B
  pr₂ (x , y) = y

  data ⊤ : Set where
    tt : ⊤

  data _∨_ (A B : Set) : Set where
    inl : A → A ∨ B
    inr : B → A ∨ B

  case_of_or_ : {A B C : Set} → A ∨ B → (A → C) → (B → C)  → C
  case inl x of p1 or p2 = p1 x
  case inr x of p1 or p2 = p2 x

  data ⊥ : Set where

  abort : {A : Set} → ⊥ → A
  abort ()

  -- Negation
  -- it is defined as A → ⊥

  ¬ : Set → Set
  ¬ A = A → ⊥
