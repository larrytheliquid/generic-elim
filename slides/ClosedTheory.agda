{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.Nat
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module ClosedTheory where

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : {I : Set} (D : Desc I) → ISet I → ISet I
El (End j) X i = j ≡ i
El (Rec j D) X i = X j × El D X i
El (Arg A B) X i = Σ A (λ a → El (B a) X i)

----------------------------------------------------------------------

UncurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedEl D X = ∀{i} → El D X i → X i

CurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedEl (End i) X = X i
CurriedEl (Rec i D) X = (x : X i) → CurriedEl D X
CurriedEl (Arg A B) X = (a : A) → CurriedEl (B a) X

CurriedEl' : {I : Set} (D : Desc I) (X : ISet I) (i : I) → Set
CurriedEl' (End j) X i = j ≡ i → X i
CurriedEl' (Rec j D) X i = (x : X j) → CurriedEl' D X i
CurriedEl' (Arg A B) X i = (a : A) → CurriedEl' (B a) X i

curryEl : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedEl D X → CurriedEl D X
curryEl (End i) X cn = cn refl
curryEl (Rec i D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A B) X cn = λ a → curryEl (B a) X (λ xs → cn (a , xs))

uncurryEl : {I : Set} (D : Desc I) (X : ISet I)
  → CurriedEl D X → UncurriedEl D X
uncurryEl (End i) X cn refl = cn
uncurryEl (Rec i D) X cn (x , xs) = uncurryEl D X (cn x) xs
uncurryEl (Arg A B) X cn (a , xs) = uncurryEl (B a) X (cn a) xs

----------------------------------------------------------------------

data μ {I : Set} (D : Desc I) : ISet I where
  init : UncurriedEl D (μ D)

Inj : {I : Set} (D : Desc I) → Set
Inj D = CurriedEl D (μ D)

inj : {I : Set} (D : Desc I) → Inj D
inj D = curryEl D (μ D) init

----------------------------------------------------------------------

data VecT : Set where
  nilT consT : VecT

VecC : (A : Set) → VecT → Desc ℕ
VecC A nilT = End zero
VecC A consT = Arg ℕ (λ n → Arg A λ _ → Rec n (End (suc n)))

nilD : (A : Set) → Desc ℕ
nilD A = End zero

consD : (A : Set) → Desc ℕ
consD A = Arg ℕ (λ n → Arg A (λ _ → Rec n (End (suc n))))

VecD : (A : Set) → Desc ℕ
VecD A = Arg VecT (VecC A)

Vec : (A : Set) → ℕ → Set
Vec A = μ (VecD A)

nil : (A : Set) → Vec A zero
nil A = init (nilT , refl)

cons : (A : Set) (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = init (consT , n , x , xs , refl)

nil2 : (A : Set) → Vec A zero
nil2 A = inj (VecD A) nilT

cons2 : (A : Set) (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons2 A = inj (VecD A) consT

----------------------------------------------------------------------
