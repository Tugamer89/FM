

module Vectors where 
  open import BasicInd renaming ( [] to []ₗ ; _∷_ to _∷ₗ_ )   

  data Vec (A : Set) : Nat → Set where 
    [] : Vec A zero 
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n) 

  -- concatenation of vectors 
  _++_ : {A : Set} → ∀ {n m} → Vec A n → Vec A m → Vec A (n + m) 
  v ++ w = {!   !} 

-- write conversion functions  between lists and vectors

-- vmap applies the function to all the elements of the input vector 
  vmap : {A B : Set} → (A → B) → ∀ {n} → Vec A n → Vec B n 
  vmap f v = {!   !}  

-- vzipWith builds a new vector by applying the function to the elements in the same position in the two input vectors 
  vzipWith : {A B C : Set} → (A → B → C) → ∀ {n} → Vec A n → Vec B n → Vec C n 
  vzipWith f v w = {!   !} 
  
  -- The type of matrices represented as a vector of columns 
  Mat : Set → Nat → Nat → Set 
  Mat A n m = Vec (Vec A n) m

  -- matrix transposition 
  transpose : {A : Set} → ∀ {n m} → Mat A n m → Mat A m n 
  transpose M = {!   !}  

  -- matrix addition (you may need to introduce addition of vectors) 
  _⊕_ : ∀ {n m} → Mat Nat n m → Mat Nat n m → Mat Nat n m 
  M1 ⊕ M2 = {!   !}  

  -- matrix multiplication (you may need to define auxiliary functions) 
  -- note the type of the function 
  _⊗_ : ∀ {n m k} → Mat Nat n k → Mat Nat k m → Mat Nat n m 
  M1 ⊗ M2 = {!   !} 