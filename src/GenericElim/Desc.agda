{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module GenericElim.Desc where

----------------------------------------------------------------------

elimEq : (A : Set) (x : A) (P : (y : A) → x ≡ y → Set)
  → P x refl
  → (y : A) (p : x ≡ y) → P y p
elimEq A .x P prefl x refl = prefl

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Branches : (E : Enum) (P : Tag E → Set) → Set
Branches [] P = ⊤
Branches (l ∷ E) P = P here × Branches E (λ t → P (there t))

case : {E : Enum} (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case P (c , cs) here = c
case P (c , cs) (there t) = case (λ t → P (there t)) cs t

UncurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedBranches E P X = Branches E P → X

CurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedBranches [] P X = X
CurriedBranches (l ∷ E) P X = P here → CurriedBranches E (λ t → P (there t)) X

curryBranches : {E : Enum} {P : Tag E → Set} {X : Set}
  (f : UncurriedBranches E P X) → CurriedBranches E P X
curryBranches {[]} f = f tt
curryBranches {l ∷ E} f = λ c → curryBranches (λ cs → f (c , cs))

uncurryBranches : {E : Enum} {P : Tag E → Set} {X : Set}
  (f : CurriedBranches E P X) → UncurriedBranches E P X
uncurryBranches {[]} x tt = x
uncurryBranches {l ∷ E} f (c , cs) = uncurryBranches (f c) cs

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I
  RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

_⇒_ : {I : Set} → ISet I → ISet I → Set
X ⇒ Y = ∀{i} → X i → Y i

IFunc : Set → Set₁
IFunc I = ISet I → ISet I

El : {I : Set} (D : Desc I) → IFunc I
El (End j) X i = j ≡ i
El (Rec j D) X i = X j × El D X i
El (Arg A B) X i = Σ A (λ a → El (B a) X i)
El (RecFun A B D) X i = ((a : A) → X (B a)) × El D X i

_∣_∣_⇛_ : {I : Set} (D : Desc I) (X : ISet I) (P Q : (i : I) → El D X i → Set) → Set
D ∣ X ∣ P ⇛ Q  = ∀ i → (xs : El D X i) → P i xs → Q i xs

Hyps : {I : Set} (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D) X P i (x , xs) = P j x × Hyps D X P i xs
Hyps (Arg A B) X P i (a , b) = Hyps (B a) X P i b
Hyps (RecFun A B D) X P i (f , xs) = ((a : A) → P (B a) (f a)) × Hyps D X P i xs

----------------------------------------------------------------------

BranchesD : (I : Set) (E : Enum) → Set
BranchesD I E = Branches E (λ _ → Desc I)

caseD : {I : Set} {E : Enum} (cs : BranchesD I E) (t : Tag E) → Desc I
caseD = case (λ _ → Desc _)

----------------------------------------------------------------------

TagDesc : (I : Set) → Set
TagDesc I = Σ Enum (BranchesD I)

toCase : {I : Set} (E,cs : TagDesc I) → Tag (proj₁ E,cs) → Desc I
toCase (E , cs) = caseD cs

toDesc : {I : Set} → TagDesc I → Desc I
toDesc (E , cs) = Arg (Tag E) (toCase (E , cs))

----------------------------------------------------------------------

UncurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedEl D X = El D X ⇒ X

CurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedEl (End i) X = X i
CurriedEl (Rec j D) X = (x : X j) → CurriedEl D X
CurriedEl (Arg A B) X = (a : A) → CurriedEl (B a) X
CurriedEl (RecFun A B D) X = ((a : A) → X (B a)) → CurriedEl D X

curryEl : {I : Set} (D : Desc I) (X : ISet I)
  (cn : UncurriedEl D X) → CurriedEl D X
curryEl (End i) X cn = cn refl
curryEl (Rec i D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A B) X cn = λ a → curryEl (B a) X (λ xs → cn (a , xs))
curryEl (RecFun A B D) X cn = λ f → curryEl D X (λ xs → cn (f , xs))

uncurryEl : {I : Set} (D : Desc I) (X : ISet I)
  (cn : CurriedEl D X) → UncurriedEl D X
uncurryEl (End i) X cn refl = cn
uncurryEl (Rec i D) X cn (x , xs) = uncurryEl D X (cn x) xs
uncurryEl (Arg A B) X cn (a , xs) = uncurryEl (B a) X (cn a) xs
uncurryEl (RecFun A B D) X cn (f , xs) = uncurryEl D X (cn f) xs

----------------------------------------------------------------------

UncurriedAlg : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
UncurriedAlg D X P cn =
  D ∣ X ∣ Hyps D X P ⇛ (λ i → P i ∘ cn)
  -- ∀ i → (xs : El D X i) (ihs : Hyps D X P i xs) → P i (cn xs)

CurriedAlg : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
CurriedAlg (End i) X P cn =
  P i (cn refl)
CurriedAlg (Rec i D) X P cn =
  (x : X i) → P i x → CurriedAlg D X P (λ xs → cn (x , xs))
CurriedAlg (Arg A B) X P cn =
  (a : A) → CurriedAlg (B a) X P (λ xs → cn (a , xs))
CurriedAlg (RecFun A B D) X P cn =
  (f : (a : A) → X (B a)) (ihf : (a : A) → P (B a) (f a)) → CurriedAlg D X P (λ xs → cn (f , xs))

curryAlg : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (pf : UncurriedAlg D X P cn)
  → CurriedAlg D X P cn
curryAlg (End i) X P cn pf =
  pf i refl tt
curryAlg (Rec i D) X P cn pf =
  λ x ih → curryAlg D X P (λ xs → cn (x , xs)) (λ i xs ihs → pf i (x , xs) (ih , ihs))
curryAlg (Arg A B) X P cn pf =
  λ a → curryAlg (B a) X P (λ xs → cn (a , xs)) (λ i xs ihs → pf i (a , xs) ihs)
curryAlg (RecFun A B D) X P cn pf =
  λ f ihf → curryAlg D X P (λ xs → cn (f , xs)) (λ i xs ihs → pf i (f , xs) (ihf , ihs))

uncurryAlg : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (pf : CurriedAlg D X P cn)
  → UncurriedAlg D X P cn
uncurryAlg (End .i) X P cn pf i refl tt =
  pf
uncurryAlg (Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryAlg D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryAlg (Arg A B) X P cn pf i (a , xs) ihs =
  uncurryAlg (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs
uncurryAlg (RecFun A B D) X P cn pf i (f , xs) (ihf , ihs) =
  uncurryAlg D X P (λ ys → cn (f , ys)) (pf f ihf) i xs ihs

----------------------------------------------------------------------

module ExplicitMu where

  data μ {I : Set} (D : Desc I) : ISet I where
    init : El D (μ D) ⇒ μ D

module NoLevitation where

  data μ {I : Set} (D : Desc I) : ISet I where
    init : UncurriedEl D (μ D)
  
  initCurried : {I : Set} (D : Desc I) → CurriedEl D (μ D)
  initCurried D = curryEl D (μ D) init
  
----------------------------------------------------------------------
  
  ind :
    {I : Set}
    (D : Desc I)
    (P : (i : I) → μ D i → Set)
    (α : UncurriedAlg D (μ D) P init)
    (i : I)
    (x : μ D i)
    → P i x
  
  hyps :
    {I : Set}
    (D₁ : Desc I)
    (P : (i : I) → μ D₁ i → Set)
    (α : UncurriedAlg D₁ (μ D₁) P init)
    (D₂ : Desc I)
    (i : I)
    (xs : El D₂ (μ D₁) i)
    → Hyps D₂ (μ D₁) P i xs
  
  ind D P α i (init xs) = α i xs (hyps D P α D i xs)
  
  hyps D P α (End j) i q = tt
  hyps D P α (Rec j A) i (x , xs) = ind D P α j x , hyps D P α A i xs
  hyps D P α (Arg A B) i (a , b) = hyps D P α (B a) i b
  hyps D P α (RecFun A B E) i (f , xs) = (λ a → ind D P α (B a) (f a)) , hyps D P α E i xs
  
----------------------------------------------------------------------
  
  indCurried :
    {I : Set}
    (D : Desc I)
    (P : (i : I) → μ D i → Set)
    (α : CurriedAlg D (μ D) P init)
    (i : I)
    (x : μ D i)
    → P i x
  indCurried D P α i x = ind D P (uncurryAlg D (μ D) P init α) i x
  
  elimUncurried :
    {I : Set}
    (E : Enum)
    (C : Tag E → Desc I)
    → let D = Arg (Tag E) C in
    (P : (i : I) → μ D i → Set)
    → UncurriedBranches E
      (λ t → CurriedAlg (C t) (μ D) P (λ xs → init (t , xs)))
      ((i : I) (x : μ D i) → P i x)
  elimUncurried E C P cs i x =
    let D = Arg (Tag E) C in
    indCurried D P
      (case (λ t → CurriedAlg (C t) (μ D) P (λ xs → init (t , xs))) cs)
      i x
  
  elim :
    {I : Set}
    (E : Enum)
    (C : Tag E → Desc I)
    → let D = Arg (Tag E) C in
    (P : (i : I) → μ D i → Set)
    → CurriedBranches E
      (λ t → CurriedAlg (C t) (μ D) P (λ xs → init (t , xs)))
      ((i : I) (x : μ D i) → P i x)
  elim E C P = curryBranches (elimUncurried E C P)
  
----------------------------------------------------------------------
  
  module Sugared where
  
    data ℕT : Set where zeroT sucT : ℕT
    data VecT : Set where nilT consT : VecT
  
    ℕD : Desc ⊤
    ℕD = Arg ℕT λ
      { zeroT → End tt
      ; sucT → Rec tt (End tt)
      }
  
    ℕ : ⊤ → Set
    ℕ = μ ℕD
  
    zero : ℕ tt
    zero = init (zeroT , refl)
  
    suc : ℕ tt → ℕ tt
    suc n = init (sucT , n , refl)

    consD : (A : Set) → Desc (ℕ tt)
    consD A = Arg (ℕ tt) (λ n → Arg A (λ _ → Rec n (End (suc n))))

    VecC : (A : Set) → VecT → Desc (ℕ tt)
    VecC A nilT = End zero
    VecC A consT =
      Arg (ℕ tt) (λ n → Arg A (λ _ → Rec n (End (suc n))))
  
    VecD : (A : Set) → Desc (ℕ tt)
    VecD A = Arg VecT (VecC A)
  
    Vec : (A : Set) (n : ℕ tt) → Set
    Vec A n = μ (VecD A) n

    consType : (A : Set) → ℕ tt → Set
    consType A n = El (consD A) (Vec A) n

    nil : (A : Set) → Vec A zero
    nil A = init (nilT , refl)
  
    cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons A n x xs = init (consT , n , x , xs , refl)
  
----------------------------------------------------------------------
  
    add : ℕ tt → ℕ tt → ℕ tt
    add = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ
        { tt (zeroT , q) tt n → n
        ; tt (sucT , m , q) (ih , tt) n → suc (ih n)
        }
      )
      tt
  
    mult : ℕ tt → ℕ tt → ℕ tt
    mult = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ
        { tt (zeroT , q) tt n → zero
        ; tt (sucT , m , q) (ih , tt) n → add n (ih n)
        }
      )
      tt
  
    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
    append A = ind (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
      (λ
        { .(init (zeroT , refl)) (nilT , refl) ih n ys → ys
        ; .(init (sucT , m , refl)) (consT , m , x , xs , refl) (ih , tt) n ys → cons A (add m n) x (ih n ys)
        }
      )
  
    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = ind (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
      (λ
        { .(init (zeroT , refl)) (nilT , refl) tt → nil A
        ; .(init (sucT , n , refl)) (consT , n , xs , xss , refl) (ih , tt) → append A m xs (mult n m) ih
        }
      )
  
----------------------------------------------------------------------

  module Desugared where

    ℕT : Enum
    ℕT = "zero" ∷ "suc" ∷ []

    VecT : Enum
    VecT = "nil" ∷ "cons" ∷ []

    ℕC : Tag ℕT → Desc ⊤
    ℕC = caseD $
        End tt
      , Rec tt (End tt)
      , tt

    ℕD : Desc ⊤
    ℕD = Arg (Tag ℕT) ℕC

    ℕ : ⊤ → Set
    ℕ = μ ℕD

    zero : ℕ tt
    zero = init (here , refl)

    suc : ℕ tt → ℕ tt
    suc n = init (there here , n , refl)

    VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
    VecC A = caseD $
        End zero
      , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
      , tt

    VecD : (A : Set) → Desc (ℕ tt)
    VecD A = Arg (Tag VecT) (VecC A)

    Vec : (A : Set) → ℕ tt → Set
    Vec A = μ (VecD A)

    nil : (A : Set) → Vec A zero
    nil A = init (here , refl)

    cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons A n x xs = init (there here , n , x , xs , refl)
   
    nil2 : (A : Set) → Vec A zero
    nil2 A = initCurried (VecD A) here
  
    cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons2 A = initCurried (VecD A) (there here)
  
----------------------------------------------------------------------
  
    module Induction where
  
      add : ℕ tt → ℕ tt → ℕ tt
      add = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
        (λ u t,c → case
          (λ t → (c : El (ℕC t) ℕ u)
                 (ih : Hyps ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
                 → ℕ u → ℕ u
          )
          ( (λ q ih n → n)
          , (λ m,q ih,tt n → suc (proj₁ ih,tt n))
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
        tt
      
      mult : ℕ tt → ℕ tt → ℕ tt
      mult = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
        (λ u t,c → case
          (λ t → (c : El (ℕC t) ℕ u)
                 (ih : Hyps ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
                 → ℕ u → ℕ u
          )
          ( (λ q ih n → zero)
          , (λ m,q ih,tt n → add n (proj₁ ih,tt n))
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
        tt
      
      append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
      append A = ind (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
        (λ m t,c → case
          (λ t → (c : El (VecC A t) (Vec A) m)
                 (ih : Hyps (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (t , c))
                 (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
          )
          ( (λ q ih n ys → subst (λ m → Vec A (add m n)) q ys)
          , (λ m',x,xs,q ih,tt n ys →
              let m' = proj₁ m',x,xs,q
                  x = proj₁ (proj₂ m',x,xs,q)
                  q = proj₂ (proj₂ (proj₂ m',x,xs,q))
                  ih = proj₁ ih,tt
              in
              subst (λ m → Vec A (add m n)) q (cons A (add m' n) x (ih n ys))
            )
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
      
      concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
      concat A m = ind (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
        (λ n t,c → case
          (λ t → (c : El (VecC (Vec A m) t) (Vec (Vec A m)) n)
                 (ih : Hyps (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n (t , c))
                 → Vec A (mult n m)
          )
          ( (λ q ih → subst (λ n → Vec A (mult n m)) q (nil A))
          , (λ n',xs,xss,q ih,tt →
              let n' = proj₁ n',xs,xss,q
                  xs = proj₁ (proj₂ n',xs,xss,q)
                  q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
                  ih = proj₁ ih,tt
              in
              subst (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
            )
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
  
----------------------------------------------------------------------
  
    module ElimUncurriedinator where
  
      elimUncurriedℕ : (P : (ℕ tt) → Set)
        (pzero : P zero)
        (psuc : (m : ℕ tt) → P m → P (suc m))
        (n : ℕ tt)
        → P n
      elimUncurriedℕ P pzero psuc = ind ℕD (λ u n → P n)
        (λ u t,c → case
          (λ t → (c : El (ℕC t) ℕ u)
                 (ih : Hyps ℕD ℕ (λ u n → P n) u (t , c))
                 → P (init (t , c))
          )
          ( (λ q ih →
              elimEq ⊤ tt (λ u q → P (init (here , q)))
                pzero
                u q
            )
          , (λ n,q ih,tt →
              elimEq ⊤ tt (λ u q → P (init (there here , proj₁ n,q , q)))
                (psuc (proj₁ n,q) (proj₁ ih,tt))
                u (proj₂ n,q)
            )
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
        tt
  
      elimUncurriedVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
        (pnil : P zero (nil A))
        (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
        (n : ℕ tt)
        (xs : Vec A n)
        → P n xs
      elimUncurriedVec A P pnil pcons = ind (VecD A) (λ n xs → P n xs)
        (λ n t,c → case
          (λ t → (c : El (VecC A t) (Vec A) n)
                 (ih : Hyps (VecD A) (Vec A) (λ n xs → P n xs) n (t , c))
                 → P n (init (t , c))
          )
          ( (λ q ih →
              elimEq (ℕ tt) zero (λ n q → P n (init (here , q)))
                pnil
                n q
            )
          , (λ n',x,xs,q ih,tt →
              let n' = proj₁ n',x,xs,q
                  x = proj₁ (proj₂ n',x,xs,q)
                  xs = proj₁ (proj₂ (proj₂ n',x,xs,q))
                  q = proj₂ (proj₂ (proj₂ n',x,xs,q))
                  ih = proj₁ ih,tt
              in
              elimEq (ℕ tt) (suc n') (λ n q → P n (init (there here , n' , x , xs , q)))
                (pcons n' x xs ih )
                n q
            )
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
  
----------------------------------------------------------------------
  
      add : ℕ tt → ℕ tt → ℕ tt
      add = elimUncurriedℕ (λ _ → ℕ tt → ℕ tt)
        (λ n → n)
        (λ m ih n → suc (ih n))
    
      mult : ℕ tt → ℕ tt → ℕ tt
      mult = elimUncurriedℕ (λ _ → ℕ tt → ℕ tt)
        (λ n → zero)
        (λ m ih n → add n (ih n))
    
      append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
      append A = elimUncurriedVec A (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
        (λ n ys → ys)
        (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
    
      concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
      concat A m = elimUncurriedVec (Vec A m) (λ n xss → Vec A (mult n m))
        (nil A)
        (λ n xs xss ih → append A m xs (mult n m) ih)
  
----------------------------------------------------------------------
  
    module GenericElimUncurriedinator where
  
      add : ℕ tt → ℕ tt → ℕ tt
      add = elim ℕT ℕC _
        (λ n → n)
        (λ m ih n → suc (ih n))
        tt
  
      mult : ℕ tt → ℕ tt → ℕ tt
      mult = elim ℕT ℕC _
        (λ n → zero)
        (λ m ih n → add n (ih n))
        tt
  
      append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
      append A = elim VecT (VecC A) _
        (λ n ys → ys)
        (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
  
      concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
      concat A m = elim VecT (VecC (Vec A m)) _
        (nil A)
        (λ n xs xss ih → append A m xs (mult n m) ih)
  
----------------------------------------------------------------------

module Levitation where
  
  data μ {I : Set} (E : Enum) (C : BranchesD I E) : I → Set where
    init : (t : Tag E) → UncurriedEl (caseD C t) (μ E C)
  
  initCurried : {I : Set} {E : Enum} (C : BranchesD I E) (t : Tag E)
    → CurriedEl (caseD C t) (μ E C)
  initCurried C t = curryEl (caseD C t) (μ _ C) (init t)
  
----------------------------------------------------------------------
  
  ind :
    {I : Set}
    {E : Enum}
    (C : BranchesD I E)
    (P : (i : I) → μ E C i → Set)
    (α : (t : Tag E) → UncurriedAlg (caseD C t) (μ E C) P (init t))
    (i : I)
    (x : μ E C i)
    → P i x
  
  hyps :
    {I : Set}
    {E : Enum}
    (C : BranchesD I E)
    (P : (i : I) → μ E C i → Set)
    (α : (t : Tag E) → UncurriedAlg (caseD C t) (μ E C) P (init t))
    (D : Desc I)
    (i : I)
    (xs : El D (μ E C) i)
    → Hyps D (μ E C) P i xs
  
  ind C P α i (init t as) = α t i as (hyps C P α (caseD C t) i as)
  
  hyps C P α (End j) i q = tt
  hyps C P α (Rec j A) i (x , xs) = ind C P α j x , hyps C P α A i xs
  hyps C P α (Arg A B) i (a , b) = hyps C P α (B a) i b
  hyps C P α (RecFun A B D) i (f , xs) = (λ a → ind C P α (B a) (f a)) , hyps C P α D i xs
  
----------------------------------------------------------------------
  
  indCurried :
    {I : Set}
    {E : Enum}
    (C : BranchesD I E)
    (P : (i : I) → μ E C i → Set)
    (α : (t : Tag E) → CurriedAlg (caseD C t) (μ E C) P (init t))
    (i : I)
    (x : μ E C i)
    → P i x
  indCurried C P α i x =
    ind C P (λ t → uncurryAlg (caseD C t) (μ _ C) P (init t) (α t)) i x
  
  elimUncurried :
    {I : Set}
    {E : Enum}
    (C : BranchesD I E)
    (P : (i : I) → μ E C i → Set)
    → let
      Q = λ t → CurriedAlg (caseD C t) (μ E C) P (init t)
      X = (i : I) (x : μ E C i) → P i x
    in UncurriedBranches E Q X
  elimUncurried C P ds i x =
    let Q = λ t → CurriedAlg (caseD C t) (μ _ C) P (init t)
    in indCurried C P (case Q ds) i x
  
  elim :
    {I : Set}
    {E : Enum}
    (C : BranchesD I E)
    (P : (i : I) → μ E C i → Set)
    → let
      Q = λ t → CurriedAlg (caseD C t) (μ E C) P (init t)
      X = (i : I) (x : μ E C i) → P i x
    in CurriedBranches E Q X
  elim C P = curryBranches (elimUncurried C P)
  
----------------------------------------------------------------------
  
  ℕT : Enum
  ℕT = "zero" ∷ "suc" ∷ []
  
  VecT : Enum
  VecT = "nil" ∷ "cons" ∷ []
  
  ℕDs : BranchesD ⊤ ℕT
  ℕDs =
      End tt
    , Rec tt (End tt)
    , tt
  
  ℕ : ⊤ → Set
  ℕ = μ ℕT ℕDs
  
  zero : ℕ tt
  zero = init here refl
  
  suc : ℕ tt → ℕ tt
  suc n = init (there here) (n , refl)
  
  zero2 : ℕ tt
  zero2 = initCurried ℕDs here
  
  suc2 : ℕ tt → ℕ tt
  suc2 = initCurried ℕDs (there here)
  
  VecDs : (A : Set) → BranchesD (ℕ tt) VecT
  VecDs A =
      End zero
    , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
    , tt
  
  Vec : (A : Set) (n : ℕ tt) → Set
  Vec A n = μ VecT (VecDs A) n
  
  nil : (A : Set) → Vec A zero
  nil A = init here refl
  
  cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons A n x xs = init (there here) (n , x , xs , refl)
  
  nil2 : (A : Set) → Vec A zero
  nil2 A = initCurried (VecDs A) here
  
  cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons2 A = initCurried (VecDs A) (there here)
  
----------------------------------------------------------------------
  
  add : ℕ tt → ℕ tt → ℕ tt
  add = elim ℕDs _
    (λ n → n)
    (λ m ih n → suc (ih n))
    tt
  
  mult : ℕ tt → ℕ tt → ℕ tt
  mult = elim ℕDs _
    (λ n → zero)
    (λ m ih n → add n (ih n))
    tt
  
  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
  append A = elim (VecDs A) _
    (λ n ys → ys)
    (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
  
  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elim (VecDs (Vec A m)) _
    (nil A)
    (λ n xs xss ih → append A m xs (mult n m) ih)
  
----------------------------------------------------------------------
