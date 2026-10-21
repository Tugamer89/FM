{- --without-K -}

module DependentTypes where
  open import SimpleTypes

-- here we introduce type formers, canonical elements
-- and eliminators for Σ, Π and Id types
-- ignore definitions, just use constructors (inside data definitions) and eliminators

-----------------
-- Identity type
-----------------

  infix 3 _==_

  data _==_ {A : Set} (a : A) : A → Set where
    rfl : a == a  -- this is the reflexivity

-- Martin-Löf's eliminator

  J : {A : Set} (B : {x x' : A} (u : x == x') → Set) (d : (x : A) → B (rfl {a = x}))
      {a a' : A} (p : a == a') → B p

  J B d rfl = d _


-- Paulin-Mohring's eliminator

  PM : {A : Set} {a : A} (B : (x : A) (u : a == x) → Set) (d : B a rfl)
      {a' : A} (p : a == a') → B a' p

  PM B d rfl = d


----------
-- Σ-type
----------

  infix 1 _,,_ -- this is thepair constructor

  data Σ (A : Set) (B : A → Set) : Set where
    _,,_ : (a : A) → B a → Σ A B  -- this is a pair constructor
  
  -- projections for Σ-types 
  fst : {A : Set} {B : A → Set} → Σ A B → A 
  fst (a ,, b) = a 
  
  snd : {A : Set} {B : A → Set} → (z : Σ A B) → B (fst z) 
  snd (a ,, b) = b 
  
  -- dependent eliminator for Σ-types 
  Σ-elim : {A : Set}{B : A → Set}(C : Σ A B → Set)(d : (x : A) (y : B x) → C (x ,, y))
              → (z : Σ A B) → C z
  Σ-elim {A} {B} C d (a ,, b) = d a b


---------------------------
-- Dependent eliminators for ∧ and ∨
---------------------------

  ∧-elim : {A B : Set} {C : A ∧ B → Set} → (d : (a : A) → (b : B) → C (a , b))
              → (u : A ∧ B) → C u
  ∧-elim d (a , b) = d a b

  ∨-elim : {A B : Set} {C : A ∨ B → Set} → (dl : (a : A) → C (inl a)) → (dr : (b : B) → C (inr b))
              → (u : A ∨ B) → C u
  ∨-elim dl dr (inl a) = dl a
  ∨-elim dl dr (inr b) = dr b


