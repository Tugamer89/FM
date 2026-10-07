module Test where

-- Definiamo i booleani da zero (senza librerie esterne)
data Bool : Set where
    true  : Bool
    false : Bool

-- Funzione negazione tramite pattern matching
not : Bool -> Bool
not true  = false
not false = true

-- Funzione identità scritta come λ-astrazione (\x -> x)
id : Bool -> Bool
id = \x -> x

and : Bool -> Bool -> Bool
and true y = y
and false y = false

or : Bool -> Bool -> Bool
or true y = true
or false y = y

xor : Bool -> Bool -> Bool
xor = \x -> \y -> or (and (not x) y) (and x (not y))
