open import Data.Nat
module OpenTheory where

----------------------------------------------------------------------

data Vec (A : Set) : ℕ → Set₁ where
  nil : Vec A zero
  cons : (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)

data Vec2 : Set → ℕ → Set₁ where
  nil : (A : Set) → Vec2 A zero
  cons : (A : Set) (n : ℕ) (x : A) (xs : Vec2 A n) → Vec2 A (suc n)

elimVec : {A : Set} (P : (n : ℕ) → Vec A n → Set)
  (pnil : P zero nil)
  (pcnons : (n : ℕ) (x : A) (xs : Vec A n) → P n xs → P (suc n) (cons n x xs))
  (n : ℕ) (xs : Vec A n) → P n xs
elimVec P pnil pcons .zero nil = pnil
elimVec P pnil pcons .(suc n) (cons n x xs) = pcons n x xs (elimVec P pnil pcons n xs)

----------------------------------------------------------------------

data Tree (A B : Set) : ℕ → ℕ → Set where
  leaf₁ : A → Tree A B (suc zero) zero
  leaf₂ : B → Tree A B zero (suc zero)
  branch : (m n x y : ℕ)
    → Tree A B m n → Tree A B x y
    → Tree A B (m + x) (n + y)

----------------------------------------------------------------------
