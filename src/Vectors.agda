

module Vectors where 
  open import BasicInd renaming ( [] to []ₗ ; _∷_ to _∷ₗ_ ; _++_ to _++ₗ_ )   

  data Vec (A : Set) : Nat → Set where 
    [] : Vec A zero 
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n) 

-- concatenation of vectors 
  _++_ : {A : Set} → ∀ {n m} → Vec A n → Vec A m → Vec A (n + m) 
  [] ++ w = w
  (x ∷ v) ++ w = x ∷ (v ++ w) 

-- write conversion functions  between lists and vectors
  vecToList : {A : Set} → ∀ {n} → Vec A n → List A
  vecToList [] = []ₗ
  vecToList (x ∷ l) = x ∷ₗ (vecToList l)

  listToVec : {A : Set} → (l : List A) → Vec A (length l)
  listToVec []ₗ = []
  listToVec (x ∷ₗ v) = x ∷ (listToVec v)

-- vmap applies the function to all the elements of the input vector 
  vmap : {A B : Set} → (A → B) → ∀ {n} → Vec A n → Vec B n 
  vmap f [] = []
  vmap f (x ∷ v) = (f x) ∷ (vmap f v)  

-- vzipWith builds a new vector by applying the function to the elements in the same position in the two input vectors 
  vzipWith : {A B C : Set} → (A → B → C) → ∀ {n} → Vec A n → Vec B n → Vec C n 
  vzipWith f [] [] = []
  vzipWith f (x ∷ v) (x₁ ∷ w) = (f x x₁) ∷ (vzipWith f v w) 
  
-- The type of matrices represented as a vector of columns 
  Mat : Set → Nat → Nat → Set 
  Mat A n m = Vec (Vec A n) m

-- matrix transposition 
  transpose : {A : Set} → ∀ {n m} → Mat A n m → Mat A m n 
  transpose {n = zero} [] = []
  transpose {n = suc n} [] = [] ∷ transpose {n = n} []
  transpose (v ∷ vs) = vzipWith _∷_ v (transpose vs)

-- matrix addition (you may need to introduce addition of vectors) 
  _⊕_ : ∀ {n m} → Mat Nat n m → Mat Nat n m → Mat Nat n m 
  M1 ⊕ M2 = vzipWith (vzipWith _+_) M1 M2 

-- matrix multiplication (you may need to define auxiliary functions) 
  -- note the type of the function 
  dot : ∀ {n} → Vec Nat n → Vec Nat n → Nat
  dot [] [] = zero
  dot (x ∷ v) (y ∷ w) = (x * y) + (dot v w)

  _⊗_ : ∀ {n m k} → Mat Nat n k → Mat Nat k m → Mat Nat n m 
  M1 ⊗ M2 = vmap (λ col → vmap (λ row → dot row col) (transpose M1)) M2 
