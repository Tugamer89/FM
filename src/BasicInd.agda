{-# OPTIONS --allow-unsolved-metas  #-}

module BasicInd where

  ------------------------------
  -- Booleans
  ------------------------------

  data Bool : Set where
    true  : Bool
    false : Bool

  -- simple eliminator
  if_then_else : {A : Set} → Bool → A → A → A
  if true then at else af = at
  if false then at else af = af

  -- boolean operator: negation, conjunction, disjunction, exclusive disjunction, implication
  -- the definition of these functions give so called truth tables
  not : Bool → Bool
  not true = false
  not false = true

  _and_ : Bool → Bool → Bool
  true and b2 = b2
  false and b2 = false

  _or_ : Bool → Bool → Bool
  true or b2 = true
  false or b2 = b2

  _xor_ : Bool → Bool → Bool
  true xor b2 = not b2
  false xor b2 = b2

  _impl_ : Bool → Bool → Bool
  true impl b2 = b2
  false impl b2 = true

  _dimpl_ : Bool → Bool → Bool
  true dimpl b2 = b2
  false dimpl b2 = not b2

  ------------------------------
  -- Natural numbers
  ------------------------------

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  one two : Nat
  one = suc zero
  two = suc (suc zero)

  -- addition and multiplication
  _+_ : Nat → Nat → Nat
  zero + m = m
  suc n + m = suc (n + m)

  _*_ : Nat → Nat → Nat
  zero * n = zero
  suc m * n = n + (n * m)

  -- it tests whether n <= m 
  _?≤_ : Nat → Nat → Bool
  zero ?≤ m = true
  suc n ?≤ zero = false
  suc n ?≤ suc m = n ?≤ m

  -- it checkes whether a number is even 
  even? : Nat → Bool 
  even? zero = true
  even? (suc zero) = false
  even? (suc (suc n)) = even? n 

  ------------------------------
  --  Lists
   ------------------------------

  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  -- define the length of a list 
  length : {A : Set} → List A → Nat
  length [] = zero
  length (x ∷ l) = suc (length l)

  -- define concatenation
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)

  -- List is a Monad
  eta : {A : Set} → A → List A
  eta x = x ∷ []

  _>>_ : {A B : Set} → (A → List B) → List A → List B
  f >> [] = []
  f >> (x ∷ xs) = (f x) ++ (f >> xs)

  -- map and fold 
  fmap : {A B : Set}  → (A → B) → List A → List B 
  fmap f [] = []
  fmap f (x ∷ xs) = (f x) ∷ (fmap f xs) 

  fold : {A B : Set} → (A → B → B) → B → List A → B 
  fold f x [] = x
  fold f x (x₁ ∷ xs) = fold f (f x₁ x) xs  

  -- flattens a list 
  flatten : {A : Set} → List (List A) → List A 
  flatten = fold _++_ []
  -- or 
  -- flatten = _>>_ (λ x → x)
  
  ----------------------------------- 
  -- Insertion Sort 
  ----------------------------------- 
  
  -- implement the insertion sort algorithm for lists of natural numbers 
  -- hint: you will  need an auxiliary function  to insert an element in the right position 

  insert : Nat → List Nat → List Nat
  insert n [] = n ∷ []
  insert n (x ∷ l) = if (n ?≤ x) then (n ∷ (x ∷ l)) else (x ∷ (insert n l))

  isort : List Nat → List Nat 
  isort [] = []
  isort (x ∷ l) = insert x (isort l) 

  ------------------------------ 
  -- Ordered Trees
  ------------------------------ 
  
  -- the type of ordered trees with an arbitrary number of children for each node 
  data Tree (A : Set) : Set where 
    node : A → List (Tree A) → Tree A

  -- implement fmap and fold functions for trees 

  tfmap-forest : {A B : Set} → (A → B) → List (Tree A) → List (Tree B)
  tfmap        : {A B : Set} → (A → B) → Tree A → Tree B 
  
  tfmap-forest f [] = []
  tfmap-forest f (x ∷ ts) = (tfmap f x) ∷ (tfmap-forest f ts)

  tfmap f (node x c) = node (f x) (tfmap-forest f c)


  tfold-forest : {A B : Set} → (A → List B → B) → List (Tree A) → List B
  tfold        : {A B : Set} → (A → List B → B) → Tree A → B
  
  tfold-forest f [] = []
  tfold-forest f (t ∷ ts) = (tfold f t) ∷ (tfold-forest f ts)

  tfold f (node x c)= f x (tfold-forest f c)

  -- implement eta and _>>_ functions for trees   

  teta : {A : Set} → A → Tree A
  teta x = node x []

  _t>>-forest_ : {A B : Set} → (A → Tree B) → List (Tree A) → List (Tree B)
  _t>>_        : {A B : Set} → (A → Tree B) → Tree A → Tree B

  f t>>-forest [] = []
  f t>>-forest (x ∷ c) = (f t>> x) ∷ (f t>>-forest c)
  
  f t>> (node x c) with f x
  ... | node y ys = node y (ys ++ (f t>>-forest c))
