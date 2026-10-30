{-# OPTIONS --allow-unsolved-metas  #-}


module DepInd  where
  open import DependentTypes
  open import SimpleTypes
  open import IdTypes renaming (_*_ to _**_)
  open import BasicInd 

  -- here you can use pattern matching to reason by induction on datatypes

  ------------------------------
  -- Booleans
  ------------------------------

  -- true ≠ false
  Pt≠f : Bool → Set
  Pt≠f true = ⊤
  Pt≠f false = ⊥

  -- hint: use transport and the above type family
  t≠f : ¬ (true == false)
  t≠f t=f = {!   !}

  true== : Bool → Set
  true== b = true == b

  ¬t→f : ∀ {b} → ¬ (true== b) → false == b
  ¬t→f {b} ¬t==b = {!   !}

  -- dependent eliminator for Bool
  _dif_then_else_ : (P : Bool → Set) → (b : Bool) → P true → P false → P b
  P dif b then pt else pf = {!   !}

  -- properties of boolean operators
  not-not : ∀ {b} → not (not b) == b
  not-not {b} = {!   !}

-- in BasicInd.agda you should have defined bollean operations (not, and, or, ...) 
  -- state and prove commutativity, associativity and neutrality for and, or
  -- state and prove de morgan laws for and, or

  impl-or : ∀ {b1 b2} → (b1 impl b2) == ((not b1) or b2)
  impl-or {b1} {b2} = {!   !}

  dimpl-and-impl : ∀ {b1 b2} → (b1 dimpl b2) == ((b1 impl b2) and (b2 impl b1))
  dimpl-and-impl {b1} {b2} = {!   !}

  -- state and prove equalities relating xor and other operators

  ------------------------------
  -- Natural numbers
  ------------------------------

  -- suc preserves equality (like any function) 
  s=s : ∀ {n m} → n == m → suc n == suc m
  s=s n=m = {!   !}

  -- similar to t≠f
  z≠s : ∀ {n} → ¬ (zero == (suc n))
  z≠s z=s = {!   !}

  -- not easy
  s-inj : ∀ {n m} → suc n == suc m → n == m
  s-inj {n} {m} sn=sm =  {!   !}

  data _≤_ : Nat → Nat → Set where
    z≤n : ∀ {n} → zero ≤ n
    s≤s : ∀ {n m} → n ≤ m → (suc n) ≤ (suc m)

  -- reflexivity
  ≤-refl : ∀ {n m} → n == m → n ≤ m
  ≤-refl n=m = {!   !}

  -- transitivity
  ≤-trans : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
  ≤-trans n≤m m≤k = {!   !}

  -- antisymmetry
  ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n == m
  ≤-antisym n≤m m≤n = {!   !}

  -- state and prove monotonicity of + and *
  -- state and prove associativity, commutativity and distributivity of + and * (use the identity type)
  -- prove that zero and one are neutral elements of + and *

  ¬s≤z : ∀ {n} → ¬ (suc n ≤ zero)
  ¬s≤z = {!   !}

  s≤s-rev : ∀ {n m} → suc n ≤ suc m → n ≤ m
  s≤s-rev sn≤sm = {!   !}

  ≤-dec : ∀ {n m} → (n ≤ m) ∨ ¬ (n ≤ m)
  ≤-dec {n} {m} = {!   !}

  -- in BasicInd.agda you have defined a decision procedure for _≤_
  -- _?<_ : Nat → Nat → Bool 
  -- the following terms show that that decision procedure is correct 
  ?≤-sound : ∀ {n m} → true== (n ?≤ m) → n ≤ m
  ?≤-sound {n} {m} t==n?≤m = {!   !}

  ?≤-complete : ∀ {n m} → n ≤ m → true== (n ?≤ m)
  ?≤-complete {n} {m} n≤m = {!   !}

  data _<_ : Nat → Nat → Set where
    z<s : ∀ {n} → zero < (suc n) 
    s<s : ∀ {n m} → n < m → (suc n) < (suc m)

  n<sn : ∀ {n} → n < (suc n) 
  n<sn {n} = {!   !}

  <2≤ : ∀ {n m} → n < m → n ≤ m
  <2≤ n<m = {!   !}

  _>_ : Nat → Nat → Set 
  n > m = m < n 

  ≤-dic : ∀ {n m} → n ≤ m → (n == m) ∨ (n < m) 
  ≤-dic {n} {m} n≤m = {!   !}

  -- even numbers 
  data Even : Nat → Set where
    ez : Even zero  -- zero is even
    es : ∀ {n} → Even n → Even (suc (suc n))  -- if n is even, so is n+2

  even-sound : ∀ {n} → Even n → Σ Nat (λ k → n == (two * k))
  even-sound {n} even = {!   !}

  even-complete : ∀ {n k} → n == (two * k) → Even n
  even-complete {n} {k} n=2k = {!   !}

  -- state and prove the correctness of the function 
  -- ?even : Nat → Bool defined in BasicInd.agda 
  

  ------------------------------
  --  Lists
   ------------------------------

  len-∷ : {A : Set} {x : A} {l : List A}  → (length l) <  length (x ∷ l)  
  len-∷ {A} {l} = {!   !}

  -- in BasicInd.agda you have defined concatenation on lists 
  -- _++_ : {A : Set} → List A → List A → List A 
  -- prove that ++ is associative commutative and [] is its neutral element
  
  ++-≤ : {A : Set} {xs ys : List A} →  (length xs) ≤ length (xs ++ ys)
  ++-≤ {A} {xs} {ys} = {!   !} 

  -- length is a homomorphism of monoids
  len-hom : {A : Set} {xs ys : List A} → length (xs ++ ys) == ((length xs) + (length ys)) 
  len-hom {xs} {ys} = {!   !}
  
  -- predicate liftings for List
  -- ListP∀ P holds on xs iff P holds on all x in xs
  ListP∀ : {A : Set} → (A → Set) → List A → Set
  ListP∀ P xs = {!   !}

  data All {A : Set} (P : A → Set) : List A → Set where
    all-[] : All P []
    all-∷ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

  -- state and prove the  logical equivalence between All P and ListP∀ P
  --
  -- define ListP∃ P xs iff P holds on some x in xs
  -- define Ex P xs as a datatype
  -- prove they are equivalent
  --
  -- membership of an element to a list 
  data _∈_ {A : Set} : A → List A → Set where
    lz : ∀ {x l} → x ∈ (x ∷ l)  
    ls : ∀ {x y l} → x ∈ l → x ∈ (y ∷ l) 

  -- prove that
  -- 1. All P xs is logically equivalent to ∀ {x} → x ∈ xs → P x
  -- 2. Ex P xs  is logically equivalent to ∃ A (λ x → x ∈ xs ∧ P x)

  ------------------------------
  --  Finite Types
  ------------------------------

  -- elements of Fin n are the first n natural numbers (roughly)
  data Fin : Nat → Set where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

  toNat : ∀ {n} → Fin n → Nat
  toNat i = {!   !}

  fromNat : ∀ {n} → (k : Nat) → k < n → Fin n
  fromNat {n} k n>k = {!   !}

  -- the maximum element in Fin (e.g., fin-max 0 == fz, fin-max 1 == fs fz, ...)
  fin-max : (n : Nat) → Fin (suc n)
  fin-max n = {!   !}

  -- extract the i-th elmenet of a list
  -- note that using Nat instead of Fin the function would be partial (the index could be out-of-bound)
  get : {A : Set} → (l : List A) → Fin (length l) → A
  get l i = {!   !}

  get-∈ : {A : Set} {l : List A} {i : Fin (length l)}  → (get l i) ∈ l
  get-∈ {A} {l} {i} = {!   !}

  ∈-get : {A : Set} {l : List A} {x : A} → x ∈ l → Σ (Fin (length l)) (λ i → get l i == x)
  ∈-get {A} {l} {x} x∈l = {!   !}

  -- listable type
  -- a type is listable iff there is a list containing all elements of that type
  Listable : (A : Set) → Set
  Listable A = Σ (List A) (λ l → (x : A) → x ∈ l)

  -- for a listable type there exists a surjection from a finite type
  listable-to-fin : {A : Set} → Listable A
                      → Σ Nat (λ n → Σ (Fin n → A) (λ f →
                          ∀ {x} → Σ (Fin n) (λ i → f i == x)))
  listable-to-fin list = {!   !}
  -- does the converse hold?
  -- is a type with an injection into a finite type listable?

  ------------------------------
  --  Decidable Types
  ------------------------------

  -- a type is decidable if it satisfies the excluded middle
  Dec : Set → Set
  Dec A = A ∨ ¬ A

  toBool : {A : Set} → Dec A → Bool
  toBool decA = case decA of (λ _ → true) or (λ _ → false)

  isTrue : {A : Set} → Dec A → Set
  isTrue decA = true== (toBool decA)

  -- a decidable type is logically equivalent to its "booleanisation"
  fromWitness : {A : Set} → (decA : Dec A) → A → isTrue decA
  fromWitness decA a = ∨-elim {C = isTrue} (λ a → rfl) (λ ¬a → abort (¬a a)) decA

  toWitness : {A  : Set} → (decA : Dec A) → isTrue decA → A
  toWitness decA istrue = {!   !}

  -- closure properties
  ⊤-dec : Dec ⊤
  ⊤-dec = {!   !}

  ⊥-dec : Dec ⊥
  ⊥-dec = {!   !}

  ∧-dec : {A B : Set} → Dec A → Dec B → Dec (A ∧ B)
  ∧-dec decA decB = {!   !}

  ∨-dec : {A B : Set} → Dec A → Dec B → Dec (A ∨ B)
  ∨-dec decA decB = {!   !}

  →-dec : {A B : Set} → Dec A → Dec B → Dec (A → B)
  →-dec decA decB = {!   !}

  ¬-dec : {A : Set} → Dec A → Dec (¬ A)
  ¬-dec decA = {!   !}
  -- does the converse Dec (¬ A) → Dec A hold?

  -- listable types are decidable
  -- difficult: you need auxiliary lemmas
  -- hing: check whether the existing list is empty
  listable-dec : {A : Set} → Listable A → Dec A
  listable-dec listA = {!   !}

  -- a type family is decidable iff all fibres are
  PDec : {A : Set} → (P : A → Set)  → Set
  PDec P = ∀ x → Dec (P x)

  dec-true== : PDec true==
  dec-true== b = {!   !}

  -- functions A → Bool determine predicates
  from-bool-fun : {A : Set} → (A → Bool) → A → Set
  from-bool-fun χ a = true== (χ a)

  -- bollean predicates are decidable
  bool-dec : {A : Set} → (χ : A → Bool) → PDec (from-bool-fun χ)
  bool-dec χ a = {!   !}

  to-bool-fun : {A : Set} {P : A → Set} → PDec P → A → Bool
  to-bool-fun decP a = {!   !}

  -- state and prove that for a decidable predicate P
  -- P is logically equivalent to from-bool-fun (to-bool-fun P)

  -- state and proove that for a boolean function χ
  -- χ is extensionally equal to to-bool-fun (from-bool-fun χ) 

  -- extendes closure properties to decidable predicates
  -- does quantification of a decidable predicate give a decidable type?
  -- what if the predicate is over a decidable type? 
  -- what if the predicate is over a listable type? 

  IsProp IsSet DecEq : Set → Set 
  IsProp A = (x y : A) → x == y  
  IsSet A = (x y : A) → IsProp (x == y) 
  DecEq A = (x y : A) → Dec (x == y) 
  
  bool-deceq : DecEq Bool 
  bool-deceq = {!   !} 
  
  nat-deceq : DecEq Nat 
  nat-deceq = {!   !} 
  
  -- types with a decidable equality are sets  
  -- the proof is quite difficult and requires some intermediate steps  
  -- the following is a constant function 
  H : (A : Set) → DecEq A → ∀ {x y} → x == y → x == y  
  H A deceq {x} {y} p = case (deceq x y) of (λ q → q) or λ ¬q → abort (¬q p)  
  
  -- H is a constant function 
  H-const : (A : Set) → (deceq : DecEq A) 
            → ∀ {x y} → (p q : x == y) → (H A deceq p) == (H A deceq q) 
  H-const A deceq p q = {!   !} 

  -- to prove the next theorem use PM  and the groupoid laws 
  p==Hrp : (A : Set) → (deceq : DecEq A) →  ∀ {x y} → (p : x == y) 
          → p == ((H A deceq rfl) ⁱ ** (H A deceq  p))
  p==Hrp A deceq p = {!   !} 
  
  -- this is the main theorem 
  deceq→set : (A : Set) → DecEq A → IsSet A 
  deceq→set A deceq = {!   !} 
  
  -- if χ : A ∘ Bool is a decision procedure then 
  -- from-bool-fun χ has fibers that are propositions 
  bool-fun-prop : {A : Set} → (χ : A → Bool) → ∀ {x} → IsProp (from-bool-fun χ x) 
  bool-fun-prop χ = {!   !} 
  
  -- this shows that decidable predicates and boolean-valued functions 
  -- are not exactly the same: 
  -- 1. if P : A -> Set is decidable, the fibers P x are not necessarily propositions
  -- 2. if χ : A → Bool is a boolean-valued function, then the fibers from-bool-fun χ x are propositions 