{-# OPTIONS --allow-unsolved-metas  #-}

-- {-# OPTIONS --without-K  #-}

module IdTypes where
  open import SimpleTypes
  open import DependentTypes


-------------
-- transport
-------------

  transp : {A : Set} (B : A → Set) {a a' : A} → a == a' → B a → B a'
  transp B p b = {!   !} 

  infix 4 _•_-_
  _•_-_ : {A : Set} (B : A → Set) {a a' : A} → a == a' → B a → B a'
  B • p - b = transp B p b

-- action of a function f on identities (paths)
  ap : {A : Set} {B : Set} (f : A → B) {a a' : A} → a == a' → f a == f a'
  ap f {a} = {!!}

-- Identity type over an identity
  IdOver : {A : Set}{B : A → Set}{a a' : A}
              → a == a' → B a → B a' → Set
  IdOver {A} {B} p b b' = B • p - b == b'

  syntax IdOver {B = B} p b b' = b ==[ B / p ] b'

-- ap for a dependent function f
  apd : {A : Set} {B : Set} {C : B → Set} (g : A → B) (f : (x : A) → C (g x))
        {a a' : A} (p : a == a')
          → (f a) ==[ C / ap g p ] f a'
  apd g f = {!   !} 


-- Use the functions above when possible to prove the following,
-- otherwise use PM or J.

-- symmetry and transitivity of ==

  =sym : {A : Set} {a a' : A} → a == a' → a' == a
  =sym {a = a} p = {!!}

  =trans : {A : Set} {a a' a'' : A} → a == a' → a' == a'' → a == a''
  =trans {A} p q = {!!}

-- which are inversion and concatenation of identities (paths)
  infixr 8 _*_
  _*_ : {A : Set} {a a' a'' : A} → a == a' → a' == a'' → a == a''
  p * q = =trans p q
  _ⁱ : {A : Set} {a a' : A} → a == a' → a' == a
  p ⁱ = =sym p

-----------------
-- groupoid laws
-----------------

  r-id* : {A : Set}{a a' : A}(p : a == a') → p * rfl == p
  r-id* p = {!!}

  l-id* : {A : Set}{a a' : A}(p : a == a') → rfl * p == p
  l-id* p = {!!}

  l-inv* : {A : Set} {a a' : A} (p : a == a') → p ⁱ * p == rfl
  l-inv* = {!!}

  r-inv* : {A : Set} {a a' : A} (p : a == a') → p * p ⁱ == rfl
  r-inv* = {!!}

-- transport is functorial wrt concatenation
  transp-* : {A : Set}(B : A → Set){a₁ a₂ a₃ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(b : B a₁)
         → B • p₁ * p₂ - b == B • p₂ - (B • p₁ - b)
  transp-* B p₁ p₂ b = {!!}

-- associativity of concatenation
  ass* : {A : Set}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
           → p₁ * (p₂ * p₃) == (p₁ * p₂) * p₃
  ass* p₁ p₂ p₃ = {!!}

-- concatenation preserves identity
  r-ext* : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂){a₃ : A}{p₁ p₂ : a₂ == a₃}
              → p₁ == p₂ → p * p₁ == p * p₂
  r-ext* p = {!!}

  l-ext* : {A : Set}{a₂ a₃ : A}(p : a₂ == a₃){a₁ : A}{p₁ p₂ : a₁ == a₂}
              → p₁ == p₂ → p₁ * p == p₂ * p
  l-ext* p = {!!}

  ext* : {A : Set}{a₁ a₂ a₃ : A}{p₁ p₃ : a₁ == a₂}{p₂ p₄ : a₂ == a₃}
            → p₁ == p₃ → p₂ == p₄ → p₁ * p₂ == p₃ * p₄
  ext* {p₁ = p₁} {p₃} {p₂} {p₄} p₁₃ p₂₄ = {!!}


-------------------------------
-- Identity of binary products
------------------------------

  =pr₁ : {A B : Set}{z z' : A ∧ B}
          → z == z'
            → pr₁ z == pr₁ z'
  =pr₁ = {!!}

  =pr₂ : {A B : Set}{z z' : A ∧ B}
          → z == z'
            → pr₂ z == pr₂ z'
  =pr₂ = {!!}

  ∧-prop-η : {A B : Set}(z : A ∧ B)
                → (pr₁ z , pr₂ z) == z
  ∧-prop-η = {!!}

  r=pair : {A B : Set}(a : A){b b' : B}
              → b == b' → (a , b) == (a , b')
  r=pair a = {!!}

  =pair : {A B : Set}{a a' : A}{b b' : B}
              → a == a' → b == b' → (a , b) == (a' , b')
  =pair {a = a} {a'} {b} {b'} = {!!}

  =in∧ : {A B : Set}{z z' : A ∧ B}
          → pr₁ z == pr₁ z' → pr₂ z == pr₂ z'
            → z == z'
  =in∧ {z = z} {z'} = {!!}


-----------------------
-- Identity of Σ-types
-----------------------

  =fst : {A : Set}{B : A → Set}{z z' : Σ A B}
          → z == z'
            → fst z == fst z'
  =fst = {!!}

  =snd : {A : Set}{B : A → Set}{z z' : Σ A B}
          → (r : z == z')
            → snd z ==[ B / =fst r ] snd z'
  =snd = {!!}

  -- propositional η-rule for Σ types
  -- note that this does not hold for definitional equality 
  Σ-prop-η : {A : Set} {B : A → Set}
                → (z : Σ A B)
                → (fst z ,, snd z) == z
  Σ-prop-η = {!!}

  r=pairΣ : {A : Set}{B : A → Set}{a : A}{b b' : B a}
             → b == b' → (a ,, b) == (a ,, b')
  r=pairΣ {A} {B} {a} {b} {b'} = {!!}

  =pairΣ : {A : Set} {B : A → Set} {a a' : A} (p : a == a') {b : B a} {b' : B a'}
              → b ==[ B / p ] b' → (a ,, b) == (a' ,, b')
  =pairΣ {A} {B} {a} {a'} p {b} {b'} q = {!!}

  =inΣ : {A : Set} {B : A → Set} {z z' : Σ A B} (p : fst z == fst z')
              → snd z ==[ B / p ] snd z' → z == z'
  =inΣ p = {!   !}


-----------------------
-- Identity of Π-types
-----------------------

  =Πptw : {A : Set}{B : A → Set}{f f' : Π A B}
          → f == f'
            → (a : A) → f a == f' a
  =Πptw r a = {!!}

  =Πfct : {A : Set}{B : A → Set}{f f' : Π A B}
          → f == f'
            → {a a' : A} → (p : a == a') → f a ==[ B / p ] f' a'
  =Πfct r a = {!apd!}

-- the converse is known as "function extensionality"
  FunExt : (A : Set)(B : A → Set) → Set
  FunExt A B = {f f' : Π A B} → ((a : A) → f a == f' a) → f == f'



---------------------------------
-- Uniqueness of identity proofs
---------------------------------

  UIP UIPrfl : (A : Set) → Set
  UIP A = {x x' : A} (p q : x == x') → p == q
  UIPrfl A = {x : A} (l : x == x) → rfl == l

  module UIP2K (uip : {A : Set} → UIP A)
               where
    uip-rfl : {A : Set} → UIPrfl A
    uip-rfl {A} = {!!}
    K : {A : Set}(B : {x : A} → x == x → Set)(d : {x : A} → B {x} rfl)
           → {x : A} → (p : x == x) → B p
    K {A} B d {x} p = {!!}


  module K2UIP2 (K : {A : Set}(B : {x : A} → x == x → Set)(d : {x : A} → B {x} rfl)
                     {x : A} (p : x == x) → B p)
                where
    uip-rfl : {A : Set} → UIPrfl A
    uip-rfl {A} = {!!}
    uip : (A : Set) → UIP A
    uip A = {!!}
