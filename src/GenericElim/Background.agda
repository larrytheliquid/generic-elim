{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module GenericElim.Background where

----------------------------------------------------------------------

record DSF : Set where
  field
    U : Set
    El : U → Set
    Surface : (u : U) (X : El u → Set) → Set

  Internal : (u : U) (X : El u → Set) → Set
  Internal u X = (xs : El u) → X xs

  field
    surface : (u : U) (X : El u → Set) → Internal u X → Surface u X
    internal : (u : U) (X : El u → Set) → Surface u X → Internal u X

----------------------------------------------------------------------

infix 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc n = x * (x ^ n)

toBool : ℕ → Bool
toBool zero = false
toBool (suc n) = true

Bits : ℕ → Set
Bits = Vec Bool

base10 : (n : ℕ) → Vec Bool n → ℕ
base10 zero [] = 0
base10 (suc n) (false ∷ bs) = base10 n bs
base10 (suc n) (true ∷ bs) = 2 ^ n + base10 n bs

internal-char : Bits 8 → ℕ
internal-char = base10 8

test-base10 : 42 ≡ internal-char (false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ [])
test-base10 = refl

InternalBits : (n : ℕ) → Set → Set
InternalBits n X = Bits n → X

SurfaceBits : (n : ℕ) → Set → Set
SurfaceBits zero X = X
SurfaceBits (suc n) X = ℕ → SurfaceBits n X

surfaceBits : (n : ℕ) (X : Set) → InternalBits n X → SurfaceBits n X
surfaceBits zero X f = f []
surfaceBits (suc n) X f b = surfaceBits n X (λ bs → f (toBool b ∷ bs))

internalBits : (n : ℕ) (X : Set) → SurfaceBits n X → InternalBits n X
internalBits zero X x [] = x
internalBits (suc n) X f (b ∷ bs) = internalBits n X (f n) bs

bits : (n : ℕ) → SurfaceBits n ℕ
bits n = surfaceBits n ℕ (λ bs → base10 n bs)

char : SurfaceBits 8 ℕ
char = bits 8

test-bits : 42 ≡ char 0 0 1 0 1 0 1 0
test-bits = refl

----------------------------------------------------------------------
