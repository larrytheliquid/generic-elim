{-# OPTIONS --type-in-type #-}
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding ( T )
open import Data.Product hiding ( curry ; uncurry )
open import Data.Nat
open import Data.String
open import Relation.Binary.PropositionalEquality using ( refl ; _≢_ ; _≡_ )
open import Function
module ClosedTheory2 where

----------------------------------------------------------------------

data Tel : Set₁ where
  Emp : Tel
  Ext : (A : Set) (B : A → Tel) → Tel

Scope : Tel → Set
Scope Emp = ⊤
Scope (Ext A B) = Σ A λ a → Scope (B a)

----------------------------------------------------------------------

UncurriedScope : (T : Tel) (X : Scope T → Set) → Set
UncurriedScope T X = (xs : Scope T) → X xs

CurriedScope : (T : Tel) (X : Scope T → Set) → Set
CurriedScope Emp X = X tt
CurriedScope (Ext A B) X = (a : A) → CurriedScope (B a) (λ b → X (a , b))

curryScope : (T : Tel) (X : Scope T → Set) → UncurriedScope T X → CurriedScope T X
curryScope Emp X f = f tt
curryScope (Ext A B) X f a = curryScope (B a) (λ b → X (a , b)) (λ b → f (a , b))

uncurryScope : (T : Tel) (X : Scope T → Set) → CurriedScope T X → UncurriedScope T X
uncurryScope Emp X x tt = x
uncurryScope (Ext A B) X f (a , b) = uncurryScope (B a) (λ b → X (a , b)) (f a) b

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

data μ {I : Set} (D : Desc I) (i : I) : Set where
  init : El D (μ D) i → μ D i

----------------------------------------------------------------------

UncurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedEl D X = ∀{i} → El D X i → X i

CurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedEl (End i) X = X i
CurriedEl (Rec i D) X = (x : X i) → CurriedEl D X
CurriedEl (Arg A B) X = (a : A) → CurriedEl (B a) X

curryEl : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedEl D X → CurriedEl D X
curryEl (End i) X cn = cn refl
curryEl (Rec i D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A B) X cn = λ a → curryEl (B a) X (λ xs → cn (a , xs))

----------------------------------------------------------------------

record Data : Set₁ where
  field
    E : Set
    P : Tel
    I : Scope P → Tel
    C : (p : Scope P) (t : E) → Desc (Scope (I p))

----------------------------------------------------------------------

  UncurriedFormer : Set
  UncurriedFormer =
    UncurriedScope P λ p
    → UncurriedScope (I p) λ i
    → Set

  FormUncurried : UncurriedFormer
  FormUncurried p = μ (Arg E (C p))

  Former : Set
  Former = CurriedScope P λ p → CurriedScope (I p) λ i → Set

  Form : Former
  Form =
    curryScope P (λ p → CurriedScope (I p) λ i → Set) λ p →
    curryScope (I p) (λ i → Set) λ i →
    FormUncurried p i

----------------------------------------------------------------------

  InjUncurried : E → Set
  InjUncurried t = UncurriedScope P λ p → CurriedEl (C p t ) (FormUncurried p)

  injUncurried : (t : E) → InjUncurried t
  injUncurried t p = curryEl (C p t)
    (FormUncurried p)
    (λ xs → init (t , xs))

  Inj : E → Set
  Inj t = CurriedScope P λ p → CurriedEl (C p t) (FormUncurried p)

  inj : (t : E) → Inj t
  inj t = curryScope P
    (λ p → CurriedEl (C p t) (FormUncurried p))
    (injUncurried t)

----------------------------------------------------------------------

open Data using ( Former ; Form ; Inj ; inj )

data VecT : Set where
  nilT consT : VecT

VecR : Data
VecR = record {
    E = VecT
  ; P = Ext Set λ _ → Emp
  ; I = λ _ → Ext ℕ λ _ → Emp
  ; C = λ { (A , tt) → λ
    { nilT → End (zero , tt)
    ; consT → Arg ℕ λ n → Arg A λ _ → Rec (n , tt) (End (suc n , tt))
    } }
  }

Vec : (A : Set) → ℕ → Set
Vec = Form VecR

nil : (A : Set) → Vec A zero
nil = inj VecR nilT

cons : (A : Set) (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons = inj VecR consT

----------------------------------------------------------------------
