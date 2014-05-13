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

record Wrapper : Set where
  field
    U : Set
    El : U → Set
    Wrapped : (u : U) (X : El u → Set) → Set

  Unwrapped : (u : U) (X : El u → Set) → Set
  Unwrapped u X = (xs : El u) → X xs

  field
    wrap : (u : U) (X : El u → Set) → Unwrapped u X → Wrapped u X
    unwrap : (u : U) (X : El u → Set) → Wrapped u X → Unwrapped u X

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

decimal : (n : ℕ) → Vec Bool n → ℕ
decimal zero [] = 0
decimal (suc n) (false ∷ bs) = decimal n bs
decimal (suc n) (true ∷ bs) = 2 ^ n + decimal n bs

unwrap-char : Bits 8 → ℕ
unwrap-char = decimal 8

test-decimal : 42 ≡ unwrap-char (false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ [])
test-decimal = refl

UnwrappedBits : (n : ℕ) → Set → Set
UnwrappedBits n X = Bits n → X

WrappedBits : (n : ℕ) → Set → Set
WrappedBits zero X = X
WrappedBits (suc n) X = ℕ → WrappedBits n X

wrapBits : (n : ℕ) (X : Set) → UnwrappedBits n X → WrappedBits n X
wrapBits zero X f = f []
wrapBits (suc n) X f b = wrapBits n X (λ bs → f (toBool b ∷ bs))

unwrapBits : (n : ℕ) (X : Set) → WrappedBits n X → UnwrappedBits n X
unwrapBits zero X x [] = x
unwrapBits (suc n) X f (b ∷ bs) = unwrapBits n X (f n) bs

bits : (n : ℕ) → WrappedBits n ℕ
bits n = wrapBits n ℕ (λ bs → decimal n bs)

char : WrappedBits 8 ℕ
char = bits 8

test-bits : 42 ≡ char 0 0 1 0 1 0 1 0
test-bits = refl

----------------------------------------------------------------------
