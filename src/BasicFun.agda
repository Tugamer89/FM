
module BasicFun where 
  
  -- identity function 
  id : {A : Set} → A → A 
  id = λ x → x 

  -- function composition 
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C 
  g ∘ f = λ x → g (f x) 

  -- S and K combinators 
  K : {A B : Set} → A → B → A 
  K = λ x → λ y → x 

  S : {A B C : Set} → (A → B → C) → (A → B) → A → C 
  S = λ x → λ y → λ z → x z (y z) 
  
  -- Church encodings  over a type A 
  module ChurchEncodings  (A : Set) where 
    CN : Set  -- the type of Church Numerals 
    CN = (A → A) → A → A 
    
    -- write zero, one and two as Church numerals 
    czero cone ctwo : CN 
    czero = λ s → λ z → z 
    cone = λ s → λ z → s z 
    ctwo = λ s → λ z → s (s z) 
    
    -- implement successor, addition, multiplication  over Church Numerals 
    csuc : CN → CN
    csuc = λ n → λ s → λ z → n s (s z)

    cadd cprod : CN → CN -> CN
    cadd = λ n → λ m → λ s → λ z → n s (m s z)
    cprod = λ n → λ m → λ s → λ z → n (m s) z

    CB : Set -- the type of Church booleans 
    CB = A → A → A 
    
    ctrue cfalse : CB 
    ctrue = λ x → λ y → x 
    cfalse = λ x → λ y → y 

    -- implement boolean operations on Bhurch booleans 
    cnot : CB → CB
    cnot = λ b → λ x → λ y → b y x
    
    cand cor : CB → CB → CB
    cand = λ b1 → λ b2 → λ x → λ y → b1 (b2 x y) y
    cor = λ b1 → λ b2 → λ x → λ y → b1 x (b2 x y)

    CP : Set -- type of Church pairs 
    CP = (A → A → A) → A  
    
    -- pair constructor 
    cpair : A → A → CP 
    cpair = λ x → λ y → λ p → p x y 

    -- projections 
    cpr1 cpr2 : CP → A 
    cpr1 = λ x → x (λ x → λ y → x) 
    cpr2 = λ x → x (λ x → λ y → y)   
    
    -- is it possible to implement isZero, isEven and pred functions? 
    isZero : CN → CB
    isZero = λ n → λ x → λ y → n (λ _ → y) x
