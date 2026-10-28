module FOL where
  open import SimpleTypes
  open import DependentTypes
  open import IPL


-----------------------------------------------
-- First order logic via propositions-as-types
-----------------------------------------------

-- the type of predicates over a type (which lives in the next universe)
  Pred : (S : Set) → Set₁
  Pred S = S → Set

-- universal quantification (∀ is a primitive symbol)
  ∀' : (S : Set) (P : Pred S) → Set
  ∀' S P = (s : S) → P s 

-- existential quantification
  ∃ : (S : Set) (P : Pred S) → Set
  ∃ S P = Σ S P

-- conjunction of predicates
  _∧'_ : {S : Set} → Pred S → Pred S → Pred S
  P ∧' Q = λ x → P x ∧ Q x

-- disjunction of predicates
  _∨'_ : {S : Set} → Pred S → Pred S → Pred S
  P ∨' Q = λ x → P x ∨ Q x

-- negation of predicates
  ¬' : {S : Set} → Pred S → Pred S
  ¬' P s = ¬ (P s)


  appl-witn : (S : Set) (P : Pred S)
                 → S → ∀' S P → ∃ S P
  appl-witn S P = λ witn → λ f → witn ,, f witn  -- ???

  ∃∧2∧∃ : (S : Set) → (P Q : Pred S)
            → ∃ S (P ∧' Q)
            → ∃ S P ∧ ∃ S Q
  ∃∧2∧∃ S P Q = λ e → (fst e ,, pr₁ (snd e)) , (fst e ,, pr₂ (snd e))

  ∃∨2∨∃ : (S : Set)(P Q : Pred S)
            → ∃ S (P ∨' Q)
            → ∃ S P ∨ ∃ S Q
  ∃∨2∨∃ S P Q = λ e → case (snd e) of (λ p → inl (fst e ,, p)) or (λ q → inr (fst e ,, q))

  ∨∃2∃∨ : (S : Set) (P Q : Pred S)
            → ∃ S P ∨ ∃ S Q
            → ∃ S (P ∨' Q)
  ∨∃2∃∨ S P Q = λ d → case d of
                      (λ e → (fst e ,, inl (snd e))) or
                      (λ e → (fst e ,, inr (snd e)))

  ∀∧2∧∀ : (S : Set) → (P Q : Pred S)
            → ∀' S (P ∧' Q)
            → ∀' S P ∧ ∀' S Q
  ∀∧2∧∀ S P Q = λ f → (λ s → pr₁ (f s)) , (λ s → pr₂ (f s))

  ∧∀2∀∧ : (S : Set) → (P Q : Pred S)
            → ∀' S P ∧ ∀' S Q
            → ∀' S (P ∧' Q)
  ∧∀2∀∧ S P Q = λ p → λ s → (pr₁ p s) , (pr₂ p s)

  ∨∀2∀∨ : (S : Set) (P Q : Pred S)
             → ∀' S P ∨ ∀' S Q
               → ∀' S (P ∨' Q)
  ∨∀2∀∨ S P Q = λ d → λ s → case d of (λ f → inl (f s)) or (λ f → inr (f s))

-- One of the following four facts requires ¬¬Elim (or ExMid) as an additional assumption.
-- Find it, add the assumption, and prove it.

  ∀¬2¬∃ : (S : Set) (P : Pred S)
             → ∀' S (¬' P)
               → ¬ (∃ S P)
  ∀¬2¬∃ S P = λ f → λ e → f (fst e) (snd e)

  ¬∃2∀¬ : (S : Set) (P : Pred S)
             → ¬ (∃ S P)
               → ∀' S (¬' P)
  ¬∃2∀¬ S P = λ ne → λ s → λ p → ne (s ,, p)

  postulate dne : ¬¬Elim

  ¬∀2∃¬ : (S : Set) (P : Pred S)
             → ¬ (∀' S P)
               → ∃ S (¬' P)
  ¬∀2∃¬ S P = λ nA → dne (λ nE → nA (λ s → dne (λ nP → nE (s ,, nP))))

  ∃¬2¬∀ : (S : Set) (P : Pred S)
             → ∃ S (¬' P)
               → ¬ (∀' S P)
  ∃¬2¬∀ S P = λ e → λ f → (snd e) (f (fst e))

-- Binary relations 
  Rel : Set → Set → Set₁ 
  Rel S T = S → T → Set 

-- the type-theoretic axiom of choice
  ttAC : (T S : Set) (R : Rel T S)
            → ∀' T (λ t → ∃ S (R t)) → ∃ (T → S) (λ f → ∀' T (λ t →  R t (f t)))
  ttAC T S P prem = {!   !} 

