{-# OPTIONS --guardedness #-}

module day1.part2 where

open import IO using (Main; run; readFiniteFile; putStr; _>>=_; _>>_; IO)
open import Data.String using (String; _==_; concat; lines; fromList; toList)
open import Data.Char using (Char)
open import Data.Unit using (⊤; tt)
open import Data.List using (map; foldl)
open import Data.Nat using (ℕ; _/_; _≡ᵇ_) renaming (_+_ to _+ℕ_; _<ᵇ_ to _<_)
open import Data.Integer public using (ℤ; +_; -_; _-_; -[1+_]; _/ℕ_; ∣_∣) renaming (_≤ᵇ_ to _<ℤ_; _+_ to _+ℤ_; _%ℕ_ to _%_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_)
open import Function as Func public using (_∘_; _∘₂_)
open import Data.Bool using (Bool; if_then_else_; true; false; _∧_; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to maybeMap)
open import Relation.Nullary using (Dec; yes; no; _because_; Reflects; ofʸ; ofⁿ)

ParseCharListToInt : List Char → Maybe ℕ
ParseCharListToInt x = readMaybe 10 (fromList x)

F3 : List Char → Maybe ℤ
F3 [] = nothing
F3 (x ∷ l) = if (fromList (x ∷ [])) == "L" then maybeMap (-_) (maybeMap +_ (ParseCharListToInt l))
        else if (fromList (x ∷ [])) == "R" then maybeMap +_ (ParseCharListToInt l)
        else nothing

F2 : String → Maybe ℤ
F2 x = F3 (toList x)

_≡ᵇℤ_ : ℤ → ℤ → Bool
+_ x ≡ᵇℤ +_ y = x ≡ᵇ y
+_ x ≡ᵇℤ -[1+_] y = false
-[1+_] x ≡ᵇℤ +_ y = false
-[1+_] x ≡ᵇℤ -[1+_] y = x ≡ᵇ y

FT⇒01_ : Bool → ℕ
FT⇒01 Bool.false = 0
FT⇒01 Bool.true = 1

G : ℤ × ℕ → ℤ → ℤ × ℕ
G (dialPos , countOfTimesAt0) (+ posMovement) = ((+ posMovement) +ℤ dialPos) , (posMovement / 100) +ℕ FT⇒01 (99 < (dialPos % 100) +ℕ (+ posMovement % 100)) +ℕ countOfTimesAt0
G (dialPos , countOfTimesAt0) (-[1+ NegMovementMinusOne ]) = ((- + negMovement) +ℤ dialPos) , (negMovement / 100) +ℕ FT⇒01 ((not ((dialPos % 100) ≡ᵇ 0)) ∧ ((dialPos % 100) < (1 +ℕ (+ negMovement % 100)))) +ℕ countOfTimesAt0
  where negMovement = 1 +ℕ NegMovementMinusOne
PICK₂ : ℤ × ℕ → ℕ
PICK₂ (_ , x) = x

any : {A : Set} → List (Maybe A) → Maybe (List A)
any [] = just []

any (just x ∷ l) with any l
any (just x ∷ l) | just newL  = just (x ∷ newL)
any (just x ∷ l) | nothing = nothing

any (nothing ∷ l) = nothing

F : String → Maybe ℕ
F x = ((maybeMap PICK₂) (maybeMap (foldl G (+ 50 , 0)) movements))
  where
    movements = any (map F2 (lines x))

Format : Maybe ℕ → String
Format (just x) = show x
Format nothing = "Error"

main : Main
main = run
  (
    readFiniteFile "input.txt"
    >>= putStr ∘ Format ∘ F
  )
