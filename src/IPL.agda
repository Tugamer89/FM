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
  K = {!   !}

  S : {A B C : Set} → (A → B → C) → (A → B) → A → C
  S = {!   !}

  ∧-assoc : {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
  ∧-assoc = {!   !}

  ∧-comm : {A B : Set} → A ∧ B → B ∧ A
  ∧-comm = {!   !}

  ⊤-left1 : {A : Set} → ⊤ ∧ A → A
  ⊤-left1 = {!   !}

  ⊤-left2 : { A : Set} → A → ⊤ ∧ A
  ⊤-left2 = {!   !}

  copy : {A : Set} → A → A ∧ A
  copy = {!   !}

  discard : {A : Set} → A → ⊤
  discard = {!   !}

  -- write similar properties for ∨ and ⊥

  ∧∨-dist : {A B C : Set} → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
  ∧∨-dist = {!   !}

  ∨∧-dist : {A B C : Set} → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
  ∨∧-dist = {!   !}

  -- do the reverse statements hold?

  curry : {A B C : Set} → (A → B → C) → A ∧ B → C
  curry = {!   !}

  uncurry : {A B C : Set} → (A ∧ B → C) → A → B → C
  uncurry = {!   !}

  ∨→-dist : {A B C : Set} → (A ∨ B → C) → (A → C) ∧ (B → C)
  ∨→-dist = {!   !}

  →∧-dist : {A B C : Set} → (A → B ∧ C) → (A → B) ∧ (A → C)
  →∧-dist = {!   !}

  ∧→-dist : {A B C : Set} → (A → B) ∧ (A → C) → A → B ∧ C
  ∧→-dist = {!   !}

  -- Negation

  contr1 : {A : Set} → A ∧ (¬ A) → ⊥
  contr1 = {!   !}

  contr2 : {A : Set} → A → ¬ A → ⊥
  contr2 = {!   !}

  ¬¬-intro : {A : Set} → A → ¬ (¬ A)
  ¬¬-intro = {!   !}

  →-equiv : {A B : Set} → ((¬ A) ∨ B) → A → B
  →-equiv = {!   !}

  de-morgan1 : {A B : Set} → (¬ A) ∧ (¬ B) → ¬ (A ∨ B)
  de-morgan1 = {!   !}

  de-morgan2 : {A B : Set} → (¬ A) ∨ (¬ B) → ¬ (A ∧ B)
  de-morgan2 = {!   !}

  de-morgan3 : {A B : Set} → (A ∧ ¬ B) → ¬ (A → B)
  de-morgan3 = {!   !}

  ¬-rev-→ : {A B : Set} → (A → B) → ¬ B → ¬ A
  ¬-rev-→ = {!   !}

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
