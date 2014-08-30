open import Data.Nat
open import Data.Vec using ( Vec ; [] ; _∷_ )
module OpenTheory2 where

----------------------------------------------------------------------

data _∈_ {A : Set} : A → {n : ℕ} → Vec A n → Set where
  here  : {n : ℕ} {x : A} {xs : Vec A n} → x ∈ (x ∷ xs)
  there : {n : ℕ} {x y : A} {xs : Vec A n} (p : x ∈ xs) → x ∈ (y ∷ xs)

----------------------------------------------------------------------
