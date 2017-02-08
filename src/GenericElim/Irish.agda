open import Function
open import Data.Unit
open import Data.Product
module GenericElim.Irish where

----------------------------------------------------------------------

mutual
  data Desc (I : Set) (O : I → Set) : Set₁ where
    δ : (i : I) → Desc I O
    κ : (A : Set) → Desc I O
    σ : (D : Desc I O) (E : Deps D → Desc I O) → Desc I O
    π : (A : Set) (D : A → Desc I O) → Desc I O
  
  Deps : ∀{I O} → Desc I O → Set
  Deps {O = O} (δ i) = O i
  Deps (κ A) = A
  Deps (σ D E) = Σ (Deps D) (λ a → Deps (E a))
  Deps (π A D) = (a : A) → Deps (D a)

Data : (I : Set) (O : I → Set) → Set₁
Data I O = Σ (Desc I O) (λ D → Deps D → Σ I (λ i → O i))

desc : ∀{I O} → Data I O → Desc I O
desc = proj₁

-- ι : ∀{I O} (R : Data I O) → Deps (desc R) → Σ I (λ i → O i)
-- ι = proj₂

idx : ∀{I O} (R : Data I O) → Deps (desc R) → I
idx R xs = proj₁ (proj₂ R xs)

out : ∀{I O} (R : Data I O) → (xs : Deps (desc R)) → O (idx R xs)
out R xs = proj₂ (proj₂ R xs)

----------------------------------------------------------------------

mutual 
  data μ {I O} (R : Data I O) : I → Set where
    init : (xs : Args R (desc R)) → μ R (idx R (deps R (desc R) xs))
 
  Args : ∀{I O} (R : Data I O) (D : Desc I O) → Set
  Args R (δ i) = μ R i
  Args R (κ A) = A
  Args R (σ D E) = Σ (Args R D) (λ a → Args R (E (deps R D a)))
  Args R (π A D) = (a : A) → Args R (D a)
  
  deps : ∀{I O} (R : Data I O) (D : Desc I O) → Args R D → Deps D
  deps R (δ ._) (init xs) = out R (deps R (desc R) xs)
  deps R (κ A) a = a
  deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
  deps R (π A D) f = λ a → deps R (D a) (f a)

Hyps : ∀{I O} (R : Data I O) (P : (i : I) → μ R i → Set) (D : Desc I O) (xs : Args R D) → Set
Hyps R P (κ A) a = ⊤
Hyps R P (δ i) x = P i x
Hyps R P (σ D E) (xs , ys) = Hyps R P D xs × Hyps R P (E (deps R D xs)) ys
Hyps R P (π A D) f = (a : A) → Hyps R P (D a) (f a)

----------------------------------------------------------------------
