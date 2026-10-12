{-# OPTIONS --allow-unsolved-metas #-}

------------------------------------------------------------
-- This files relies on SimpleTypes.agda , 
-- have a look at it before starting. 
-- In order to have clearer correspondence with the syntax
  -- presented during lectures,  in the first place try not  
  -- to use patern matching.  
------------------------------------------------------------


module IPL where
  open import SimpleTypes

  id : {A : Set} → A → A
  id x = x  -- id = λ x → x

  compose : {A B C : Set} → (B → C) → (A → B) → A → C
  compose g f x = g (f x) -- compose = λ g → λ f → λ x → g (f x)

  K : {A B : Set} → A → B → A
  K = λ x → λ y → x

  S : {A B C : Set} → (A → B → C) → (A → B) → A → C
  S = λ f → λ g → λ x → f x (g x)

  ∧-assoc : {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
  ∧-assoc = λ x → pr₁ (pr₁ x) , (pr₂ (pr₁ x) , pr₂ x)

  ∧-comm : {A B : Set} → A ∧ B → B ∧ A
  ∧-comm = λ x → pr₂ x , pr₁ x

  ⊤-left1 : {A : Set} → ⊤ ∧ A → A
  ⊤-left1 = λ x → pr₂ x

  ⊤-left2 : { A : Set} → A → ⊤ ∧ A
  ⊤-left2 = λ x → tt , x

  copy : {A : Set} → A → A ∧ A
  copy = λ x → x , x

  discard : {A : Set} → A → ⊤
  discard = λ x → tt

  -- write similar properties for ∨ and ⊥

  ∨-assoc : {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
  ∨-assoc = λ x → case x of (λ y → case y of (λ a → inl a) or (λ b → inr (inl b))) or (λ c → inr (inr c))

  ∨-comm : {A B C : Set} → A ∨ B → B ∨ A
  ∨-comm = λ x → case x of (λ a → inr a) or (λ b → inl b)

  ⊥-left1 : {A : Set} → ⊥ ∨ A → A
  ⊥-left1 = λ x → case x of (λ b → abort b) or (λ a → a)

  ⊥-left2 : {A : Set} → A → ⊥ ∨ A
  ⊥-left2 = λ a → inr a

  absurd : {A : Set} → ⊥ → A
  absurd = λ b → abort b


  ∧∨-dist : {A B C : Set} → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
  ∧∨-dist = λ x → case pr₂ x of (λ b → inl (pr₁ x , b)) or (λ c → inr (pr₁ x , c))

  ∨∧-dist : {A B C : Set} → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
  ∨∧-dist = λ x → case x of (λ a → inl a , inl a) or (λ bc → inr (pr₁ bc) , inr (pr₂ bc))

  -- do the reverse statements hold?

  ∧∨-dist-rev : {A B C : Set} → (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C)
  ∧∨-dist-rev = λ x → case x of (λ ab → pr₁ ab , inl (pr₂ ab)) or (λ ac → pr₁ ac , inr (pr₂ ac))

  ∨∧-dist-rev : {A B C : Set} → (A ∨ B) ∧ (A ∨ C) → A ∨ (B ∧ C)
  ∨∧-dist-rev = λ x → case pr₁ x of (λ a → inl a) or (λ b → case pr₂ x of (λ a → inl a) or (λ c → inr (b , c)))


  curry : {A B C : Set} → (A → B → C) → A ∧ B → C
  curry = λ f → λ ab → f (pr₁ ab) (pr₂ ab)

  uncurry : {A B C : Set} → (A ∧ B → C) → A → B → C
  uncurry = λ f → λ a → λ b → f (a , b)

  ∨→-dist : {A B C : Set} → (A ∨ B → C) → (A → C) ∧ (B → C)
  ∨→-dist = λ f → (λ a → f (inl a)) , (λ b → f (inr b))

  →∧-dist : {A B C : Set} → (A → B ∧ C) → (A → B) ∧ (A → C)
  →∧-dist = λ f → (λ a → pr₁ (f a)) , (λ a → pr₂ (f a))

  ∧→-dist : {A B C : Set} → (A → B) ∧ (A → C) → A → B ∧ C
  ∧→-dist = λ x → λ a → pr₁ x a , pr₂ x a

  -- Negation

  contr1 : {A : Set} → A ∧ (¬ A) → ⊥
  contr1 = λ x → (pr₂ x) (pr₁ x)

  contr2 : {A : Set} → A → ¬ A → ⊥
  contr2 = λ a → λ na → na a

  ¬¬-intro : {A : Set} → A → ¬ (¬ A)  -- ¬ (¬ A) ≡ (A → ⊥) → ⊥
  ¬¬-intro = λ a → λ na → na a

  →-equiv : {A B : Set} → ((¬ A) ∨ B) → A → B
  →-equiv = λ x → λ a → case x of (λ na → abort (na a)) or (λ b → b)

  de-morgan1 : {A B : Set} → (¬ A) ∧ (¬ B) → ¬ (A ∨ B)  -- ≡ ((A → ⊥) ∧ (B → ⊥)) → (A ∨ B) → ⊥
  de-morgan1 = λ x → λ y → case y of (λ a → pr₁ x a) or (λ b → pr₂ x b)

  de-morgan2 : {A B : Set} → (¬ A) ∨ (¬ B) → ¬ (A ∧ B)  -- ≡ ((A → ⊥) ∨ (B → ⊥)) → (A ∧ B) → ⊥
  de-morgan2 = λ x → λ y → case x of (λ fa → fa (pr₁ y)) or (λ fb → fb (pr₂ y))

  de-morgan3 : {A B : Set} → (A ∧ ¬ B) → ¬ (A → B)  -- ≡ (A ∧ (B → ⊥)) → (A → B) → ⊥
  de-morgan3 = λ x → λ f → pr₂ x (f (pr₁ x))

  ¬-rev-→ : {A B : Set} → (A → B) → ¬ B → ¬ A  -- ≡ (A → B) → (B → ⊥) → (A → ⊥)
  ¬-rev-→ = λ f → λ nb → λ a → nb (f a)

  -- the following shows that the double negation of the excluded middle is provable in IPL
  -- hint: find a way to get a variable of type A in the context
  ¬¬-exmid : {A : Set} → ¬ (¬ (A ∨ ¬ A))
  ¬¬-exmid = {!   !}

  -- reduction ad absurdium

  -- type definitions
  -- a (higher) type stating that every (small) type A has the law of excluded middle
  ExMid : Set _
  ExMid = {A : Set} →  A ∨ ¬ A

  -- a (higher) type stating that every (small) type can eliminate double negation
  ¬¬Elim : Set _
  ¬¬Elim = {A : Set} →  (¬ (¬ A)) → A

  module dne-to-em where
    -- postulate the existence of a term of type ¬¬Elim
    -- that is, assume double negation elimination for all (small) types
    postulate dne : ¬¬Elim

    -- construct a term of type ExMid
    -- that is, prove the law of excluded middle for all types
    -- hint: use ¬¬-exmid
    em : ExMid
    em = {!   !}

  module em-to-dne where
    -- postulate the existence of a term of type ExMid
    -- that is, assume the law of excluded middle for all (small) types
    postulate em : ExMid

    -- construct a term of type ¬¬Elim
    -- that is, prove double negation elimination for all types
    -- hint: use case_of_or_ to split cases over em
    dne : ¬¬Elim
    dne ¬¬a = {!   !}
