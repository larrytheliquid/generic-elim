open import Function
open import Data.Unit
open import Data.Nat
open import Data.Fin renaming ( zero to here ; suc to there)
open import Data.Product
module GenericElim.Swedish3 where

----------------------------------------------------------------------

data Desc (I : Set) (O : I → Set) : Set₁ where
  ι : (i : I) (o : O i) → Desc I O
  σ : (A : Set) (D : A → Desc I O) → Desc I O
  δ : (A : Set) (i : A → I) (D : (o : (a : A) → O (i a)) → Desc I O) → Desc I O

mutual
  data μ {I O} (D : Desc I O) : I → Set where
    init : (xs : Args D D) → μ D (idx D D xs)

  Args : ∀{I O} (R D : Desc I O) → Set
  Args R (ι i o) = ⊤
  Args R (σ A D) = Σ A (λ a → Args R (D a))
  Args R (δ A i D) = Σ ((a : A) → μ R (i a)) (λ f → Args R (D (out ∘ f)))
  
  out : ∀{I O} {D : Desc I O} {i} → μ D i → O i
  out {D = D} (init xs) = out' D D xs

  idx : ∀{I O} (R D : Desc I O) (xs : Args R D) → I
  idx R (ι i o) tt = i
  idx R (σ A D) (a , xs) = idx R (D a) xs
  idx R (δ A i D) (f , xs) = idx R (D (out ∘ f)) xs

  out' : ∀{I O} (R D : Desc I O) (xs : Args R D) → O (idx R D xs)
  out' R (ι i o) tt = o
  out' R (σ A D) (a , xs) = out' R (D a) xs
  out' R (δ A i D) (f , xs) = out' R (D (λ a → out (f a))) xs

----------------------------------------------------------------------

Hyps : ∀{I O} (R : Desc I O) (P : (i : I) → μ R i → Set) (D : Desc I O) (xs : Args R D) → Set
Hyps R P (ι i o) tt = ⊤
Hyps R P (σ A D) (a , xs) = Hyps R P (D a) xs
Hyps R P (δ A i D) (f , xs) = ((a : A) → P (i a) (f a)) × Hyps R P (D (out ∘ f)) xs

----------------------------------------------------------------------

ind : ∀ {I O}
  (D : Desc I O)
  (P : (i : I) → μ D i → Set)
  (α : (xs : Args D D) → Hyps D P D xs → P (idx D D xs) (init xs))
  (i : I)
  (x : μ D i)
  → P i x

hyps : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (α : (xs : Args R R) → Hyps R P R xs → P (idx R R xs) (init xs))
  (D : Desc I O)
  (xs : Args R D)
  → Hyps R P D xs

ind D P α .(idx D D xs) (init xs) = α xs (hyps D P α D xs)

hyps R P α (ι i o) tt = tt
hyps R P α (σ A D) (a , xs) = hyps R P α (D a) xs
hyps R P α (δ A i D) (f , xs) = (λ a → ind R P α (i a) (f a))
  , hyps R P α (D (out ∘ f)) xs

----------------------------------------------------------------------

Init : ∀{I O} (R D : Desc I O) → Set
Init R D = (xs : Args R D) → μ R (idx R D xs)

Alg : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (D : Desc I O)
  (φ : Init R D)
  → Set
Alg R P D φ = (xs : Args R D) → Hyps R P D xs → P (idx R D xs) (φ xs)

Ind : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (D : Desc I O)
  (φ : Init R D)
  → Set
Ind {I = I} R P D φ = Alg R P D φ → (i : I) (x : μ R i) → P i x

----------------------------------------------------------------------

Branch : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (D : Desc I O)
  (φ : Init R D)
  → Set
Branch R P (ι i o) φ =
  P i (φ tt)
Branch R P (σ A D) φ =
  (a : A) → Branch R P (D a) (curry φ a)
Branch R P (δ A i D) φ =
  (f : (a : A) → μ R (i a))
  (g : (a : A) → P (i a) (f a))
  → Branch R P (D (out ∘ f)) (curry φ f)

alg : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (D : Desc I O)
  (φ : Init R D)
  (β : Branch R P D φ)
  → Alg R P D φ
alg R P (ι i o) φ β tt tt =
  β
alg R P (σ A D) φ β (a , xs) ps =
  alg R P (D a) (curry φ a) (β a) xs ps
alg R P (δ A i D) φ β (f , xs) (p , ps) =
  alg R P (D (out ∘ f)) (curry φ f) (β f p) xs ps

-- branch : ∀{I O}
--   (R : Desc I O)
--   (P : (i : I) → μ R i → Set)
--   (D : Desc I O)
--   (φ : Init R D)
--   (α : Alg R P D φ)
--   → Branch R P D φ
-- branch R P (ι i o) φ α = α tt tt
-- branch R P (σ A D) φ α = λ a →
--   branch R P (D a) (curry φ a) (curry α a)
-- branch R P (δ A i D) φ α = λ f g →
--   branch R P (D (out ∘ f)) (curry φ f) (λ xs ihs → α (f , xs) (g , ihs))

----------------------------------------------------------------------

Prod : (n : ℕ) (P : Fin n → Set) → Set
Prod n P = (i : Fin n) → P i

cons : {n : ℕ} {P : Fin (suc n) → Set}
  → P here
  → Prod n (P ∘ there)
  → Prod (suc n) P
cons p f here = p
cons p f (there i) = f i

Uncurried : (n : ℕ) (P : Fin n → Set) (X : Set) → Set
Uncurried n P X = Prod n P → X

Curried : (n : ℕ) (P : Fin n → Set) (X : Set) → Set
Curried zero P X = X
Curried (suc n) P X = P here → Curried n (P ∘ there) X

curries : (n : ℕ) (P : Fin n → Set) (X : Set)
  → Uncurried n P X
  → Curried n P X
curries zero P X f = f (λ())
curries (suc n) P X f = λ p →
  curries n (P ∘ there) X (f ∘ cons p)

----------------------------------------------------------------------

Branches : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (n : ℕ)
  (D : Fin n → Desc I O)
  (φ : Init R (σ (Fin n) D))
  (p : Fin n)
  → Set
Branches R P ._ D φ here =
  Branch R P (D here) (curry φ here)
Branches R P ._ D φ (there p) =
  Branches R P _ (D ∘ there) (λ { (i , xs) → φ (there i , xs) }) p

branch :  ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (n : ℕ)
  (D : Fin n → Desc I O)
  (φ : Init R (σ (Fin n) D))
  (p : Fin n)
  (β : Branches R P n D φ p)
  → Branch R P (σ (Fin n) D) φ
branch R P ._ D φ here β p = {!!}
branch R P ._ D φ (there p) β q = {!!}

Prelim : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (n : ℕ)
  (D : Fin n → Desc I O)
  (φ : Init R (σ (Fin n) D))
  → Set
Prelim {I = I} R P zero D φ =
  (i : I) (x : μ R i) → P i x
Prelim R P (suc n) D φ =
  Branch R P (D here) (curry φ here) →
  Prelim R P n (D ∘ there) (λ { (i , xs) → φ (there i , xs) })

-- ind' : ∀{I O}
--   (R : Desc I O)
--   (P : (i : I) → μ R i → Set)
--   (n : ℕ)
--   (D : Fin n → Desc I O)
--   (φ : Init R (σ (Fin n) D))
--   → Branches R P n D φ
--   → Ind R P (σ (Fin n) D) φ
-- ind' R P zero D φ β α i x =
--   β i x
-- ind' R P (suc n) D φ β α i x = ind' R P n
--   (D ∘ there)
--   (φ ∘ xs')
--   (β β')
--   (α ∘ xs')
--   i x
--   where
--   xs' = λ xs → there (proj₁ xs) , proj₂ xs
--   β' = branch R P (D here) (curry φ here) (curry α here)

prelim : ∀{I O}
  (R : Desc I O)
  (P : (i : I) → μ R i → Set)
  (n : ℕ)
  (D : Fin n → Desc I O)
  (φ : Init R (σ (Fin n) D))
  → Ind R P (σ (Fin n) D) φ
  → Prelim R P n D φ
prelim R P zero D φ ρ i x = ρ (λ {(() , xs)}) i x
prelim R P (suc n) D φ ρ β = prelim R P n (D ∘ there)
  (λ xs → φ (there (proj₁ xs) , proj₂ xs))
  (λ α i x → {!!})
  -- (λ α i x → ρ (alg R P {!D here!} {!!} {!!}) i x)

-- Elim : ∀{I O}
--   (n : ℕ)
--   (D : Fin n → Desc I O)
--   → Set₁
-- Elim n D =
--   let R = σ (Fin n) D in
--   (P : ∀ i → μ R i → Set)
--   → Branches R P n D init

-- elim : ∀{I O}
--   (n : ℕ)
--   (D : Fin n → Desc I O)
--   → Elim n D
-- elim n D P = let R = σ (Fin n) D in
--   branches R P n D init (ind R P)

----------------------------------------------------------------------
