

module SumsProds where
  open import SimpleTypes
  open import DependentTypes


  -- use the dependent eliminator Σ-elim to define projections  
  fst' : {A : Set}{B : A → Set} → Σ A B → A
  fst' {A} = {!!}

  snd' : {A : Set}{B : A → Set} → (z : Σ A B) → B (fst' z)
  snd' {B = B} = {!!}

----------------------
-- Dependent currying
----------------------

  dep-curry : {A : Set} {B : A → Set} {C : Set} → ((Σ A B) → C) → (x : A) → B x → C
  dep-curry = {!!}

  dep-uncurry : {A : Set} {B : A → Set} {C : Set} → ((x : A) → B x → C) → Σ A B → C
  dep-uncurry = {!!}

-- Π and Σ "in context"
  Πᶠ Σᶠ : {A : Set} (B : A → Set) (C : (x : A) → B x → Set) → A → Set
  Πᶠ B C a = (x : B a) → C a x 
  Σᶠ B C a = Σ (B a) (C a)
  

-- uncurried families
  uncurry-fam _ᵘ : {A : Set} {B : A → Set} → ((x : A) → B x → Set) → Σ A B → Set
  uncurry-fam C z = C (fst z) (snd z)
  C ᵘ = uncurry-fam C

-- constant family
  const-fam _ᶜ : (A : Set) {I : Set} → I → Set
  const-fam A _ = A
  A ᶜ = const-fam A

-- reindexed family
  ridx-fam _⋆ : {A : Set} {B : A → Set}  (C : (x : A) → B x → Set) 
                 → (f : (x : A) → B x) → A → Set
  ridx-fam C f a = C a (f a)
  C ⋆ = ridx-fam C

-- fully dependent currying and uncurrying
  depdep-curry : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
                    → Π (Σ A B) (C ᵘ) → Π A (Πᶠ B C) 
  depdep-curry  = {!   !}

  depdep-uncurry : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
                      → Π A (Πᶠ B C) → Π (Σ A B) (C ᵘ) 
  depdep-uncurry = {!   !} 


 
  -- distributivity of Π over Σ (aka the type theoretic Axiom of Choice)
  ΠΣ-dist : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
               → Π A (Σᶠ B C) → Σ (Π A B) (Πᶠ (A ᶜ) (C ⋆))
                                           -- (λ f → Π A (λ x → C x (f x)))
  ΠΣ-dist {A} {B} {C} prem = {!    !}


