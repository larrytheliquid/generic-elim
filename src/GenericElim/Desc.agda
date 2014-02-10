{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
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

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases [] P = ⊤
Cases (l ∷ E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (l ∷ E) P (c , cs) here = c
case (l ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

UncurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedCases E P X = Cases E P → X

CurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedCases [] P X = X
CurriedCases (l ∷ E) P X = P here → CurriedCases E (λ t → P (there t)) X

curryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : UncurriedCases E P X) → CurriedCases E P X
curryCases [] P X f = f tt
curryCases (l ∷ E) P X f = λ c → curryCases E (λ t → P (there t)) X (λ cs → f (c , cs))

uncurryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : CurriedCases E P X) → UncurriedCases E P X
uncurryCases [] P X x tt = x
uncurryCases (l ∷ E) P X f (c , cs) = uncurryCases E (λ t → P (there t)) X (f c) cs

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I
  RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : {I : Set} (D : Desc I) → ISet I → ISet I
El (End j) X i = j ≡ i
El (Rec j D) X i = X j × El D X i
El (Arg A B) X i = Σ A (λ a → El (B a) X i)
El (RecFun A B D) X i = ((a : A) → X (B a)) × El D X i

Hyps : {I : Set} (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D) X P i (x , xs) = P j x × Hyps D X P i xs
Hyps (Arg A B) X P i (a , b) = Hyps (B a) X P i b
Hyps (RecFun A B D) X P i (f , xs) = ((a : A) → P (B a) (f a)) × Hyps D X P i xs

----------------------------------------------------------------------

TagDesc : (I : Set) → Set
TagDesc I = Σ Enum (λ E → Cases E (λ _ → Desc I))

toCase : {I : Set} (E,cs : TagDesc I) → Tag (proj₁ E,cs) → Desc I
toCase {I} (E , cs) = case E (λ _ → Desc I) cs

toDesc : {I : Set} → TagDesc I → Desc I
toDesc (E , cs) = Arg (Tag E) (toCase (E , cs))

----------------------------------------------------------------------

UncurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedEl D X = ∀{i} → El D X i → X i

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

UncurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
UncurriedHyps D X P cn =
  ∀ i → (xs : El D X i) (ihs : Hyps D X P i xs) → P i (cn xs)

CurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
CurriedHyps (End i) X P cn =
  P i (cn refl)
CurriedHyps (Rec i D) X P cn =
  (x : X i) → P i x → CurriedHyps D X P (λ xs → cn (x , xs))
CurriedHyps (Arg A B) X P cn =
  (a : A) → CurriedHyps (B a) X P (λ xs → cn (a , xs))
CurriedHyps (RecFun A B D) X P cn =
  (f : (a : A) → X (B a)) (ihf : (a : A) → P (B a) (f a)) → CurriedHyps D X P (λ xs → cn (f , xs))

curryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (pf : UncurriedHyps D X P cn)
  → CurriedHyps D X P cn
curryHyps (End i) X P cn pf =
  pf i refl tt
curryHyps (Rec i D) X P cn pf =
  λ x ih → curryHyps D X P (λ xs → cn (x , xs)) (λ i xs ihs → pf i (x , xs) (ih , ihs))
curryHyps (Arg A B) X P cn pf =
  λ a → curryHyps (B a) X P (λ xs → cn (a , xs)) (λ i xs ihs → pf i (a , xs) ihs)
curryHyps (RecFun A B D) X P cn pf =
  λ f ihf → curryHyps D X P (λ xs → cn (f , xs)) (λ i xs ihs → pf i (f , xs) (ihf , ihs))

uncurryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (pf : CurriedHyps D X P cn)
  → UncurriedHyps D X P cn
uncurryHyps (End .i) X P cn pf i refl tt =
  pf
uncurryHyps (Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryHyps D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryHyps (Arg A B) X P cn pf i (a , xs) ihs =
  uncurryHyps (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs
uncurryHyps (RecFun A B D) X P cn pf i (f , xs) (ihf , ihs) =
  uncurryHyps D X P (λ ys → cn (f , ys)) (pf f ihf) i xs ihs

----------------------------------------------------------------------

module NoLevitation where

  data μ {I : Set} (D : Desc I) : I → Set where
    con : UncurriedEl D (μ D)
  
  con2 : {I : Set} (D : Desc I) → CurriedEl D (μ D)
  con2 D = curryEl D (μ D) con
  
----------------------------------------------------------------------
  
  ind :
    {I : Set}
    (D : Desc I)
    (P : (i : I) → μ D i → Set)
    (pcon : UncurriedHyps D (μ D) P con)
    (i : I)
    (x : μ D i)
    → P i x
  
  hyps :
    {I : Set}
    (D₁ : Desc I)
    (P : (i : I) → μ D₁ i → Set)
    (pcon : UncurriedHyps D₁ (μ D₁) P con)
    (D₂ : Desc I)
    (i : I)
    (xs : El D₂ (μ D₁) i)
    → Hyps D₂ (μ D₁) P i xs
  
  ind D P pcon i (con xs) = pcon i xs (hyps D P pcon D i xs)
  
  hyps D P pcon (End j) i q = tt
  hyps D P pcon (Rec j A) i (x , xs) = ind D P pcon j x , hyps D P pcon A i xs
  hyps D P pcon (Arg A B) i (a , b) = hyps D P pcon (B a) i b
  hyps D P pcon (RecFun A B E) i (f , xs) = (λ a → ind D P pcon (B a) (f a)) , hyps D P pcon E i xs
  
----------------------------------------------------------------------
  
  ind2 :
    {I : Set}
    (D : Desc I)
    (P : (i : I) → μ D i → Set)
    (pcon : CurriedHyps D (μ D) P con)
    (i : I)
    (x : μ D i)
    → P i x
  ind2 D P pcon i x = ind D P (uncurryHyps D (μ D) P con pcon) i x
  
  elim :
    {I : Set}
    (TD : TagDesc I)
    → let
      D = toDesc TD
      E = proj₁ TD
      Cs = toCase TD
    in (P : (i : I) → μ D i → Set)
    → let
      Q = λ t → CurriedHyps (Cs t) (μ D) P (λ xs → con (t , xs))
      X = (i : I) (x : μ D i) → P i x
    in UncurriedCases E Q X
  elim TD P cs i x =
    let
      D = toDesc TD
      E = proj₁ TD
      Cs = toCase TD
      Q = λ t → CurriedHyps (Cs t) (μ D) P (λ xs → con (t , xs))
      p = case E Q cs
    in ind2 D P p i x
  
  elim2 :
    {I : Set}
    (TD : TagDesc I)
    → let
      D = toDesc TD
      E = proj₁ TD
      Cs = toCase TD
    in (P : (i : I) → μ D i → Set)
    → let
      Q = λ t → CurriedHyps (Cs t) (μ D) P (λ xs → con (t , xs))
      X = (i : I) (x : μ D i) → P i x
    in CurriedCases E Q X
  elim2 TD P =
    let
      D = toDesc TD
      E = proj₁ TD
      Cs = toCase TD
      Q = λ t → CurriedHyps (Cs t) (μ D) P (λ xs → con (t , xs))
      X = ∀ i → (x : μ D i) → P i x
    in curryCases E Q X (elim TD P)
  
----------------------------------------------------------------------
  
  module Sugared where
  
    data ℕT : Set where `zero `suc : ℕT
    data VecT : Set where `nil `cons : VecT
  
    ℕD : Desc ⊤
    ℕD = Arg ℕT λ
      { `zero → End tt
      ; `suc → Rec tt (End tt)
      }
  
    ℕ : ⊤ → Set
    ℕ = μ ℕD
  
    zero : ℕ tt
    zero = con (`zero , refl)
  
    suc : ℕ tt → ℕ tt
    suc n = con (`suc , n , refl)
  
    VecD : (A : Set) → Desc (ℕ tt)
    VecD A = Arg VecT λ
      { `nil  → End zero
      ; `cons → Arg (ℕ tt) λ n → Arg A λ _ → Rec n (End (suc n))
      }
  
    Vec : (A : Set) (n : ℕ tt) → Set
    Vec A n = μ (VecD A) n
  
    nil : (A : Set) → Vec A zero
    nil A = con (`nil , refl)
  
    cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons A n x xs = con (`cons , n , x , xs , refl)
  
----------------------------------------------------------------------
  
    add : ℕ tt → ℕ tt → ℕ tt
    add = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ
        { tt (`zero , q) tt n → n
        ; tt (`suc , m , q) (ih , tt) n → suc (ih n)
        }
      )
      tt
  
    mult : ℕ tt → ℕ tt → ℕ tt
    mult = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ
        { tt (`zero , q) tt n → zero
        ; tt (`suc , m , q) (ih , tt) n → add n (ih n)
        }
      )
      tt
  
    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
    append A = ind (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
      (λ
        { .(con (`zero , refl)) (`nil , refl) ih n ys → ys
        ; .(con (`suc , m , refl)) (`cons , m , x , xs , refl) (ih , tt) n ys → cons A (add m n) x (ih n ys)
        }
      )
  
    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = ind (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
      (λ
        { .(con (`zero , refl)) (`nil , refl) tt → nil A
        ; .(con (`suc , n , refl)) (`cons , n , xs , xss , refl) (ih , tt) → append A m xs (mult n m) ih
        }
      )
  
----------------------------------------------------------------------
  
  module Desugared where
  
    ℕT : Enum
    ℕT = "zero" ∷ "suc" ∷ []
    
    VecT : Enum
    VecT = "nil" ∷ "cons" ∷ []
  
    ℕTD : TagDesc ⊤
    ℕTD = ℕT
      , End tt
      , Rec tt (End tt)
      , tt
    
    ℕCs : Tag ℕT → Desc ⊤
    ℕCs = toCase ℕTD
    
    ℕD : Desc ⊤
    ℕD = toDesc ℕTD
    
    ℕ : ⊤ → Set
    ℕ = μ ℕD
    
    zero : ℕ tt
    zero = con (here , refl)
    
    suc : ℕ tt → ℕ tt
    suc n = con (there here , n , refl)
    
    zero2 : ℕ tt
    zero2 = con2 ℕD here
  
    suc2 : ℕ tt → ℕ tt
    suc2 = con2 ℕD (there here)
  
    VecTD : (A : Set) → TagDesc (ℕ tt)
    VecTD A = VecT
      , End zero
      , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
      , tt
  
    VecCs : (A : Set) → Tag VecT → Desc (ℕ tt)
    VecCs A = toCase (VecTD A)
    
    VecD : (A : Set) → Desc (ℕ tt)
    VecD A = toDesc (VecTD A)
    
    Vec : (A : Set) (n : ℕ tt) → Set
    Vec A n = μ (VecD A) n
    
    nil : (A : Set) → Vec A zero
    nil A = con (here , refl)
    
    cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons A n x xs = con (there here , n , x , xs , refl)
   
    nil2 : (A : Set) → Vec A zero
    nil2 A = con2 (VecD A) here
  
    cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
    cons2 A = con2 (VecD A) (there here)
  
----------------------------------------------------------------------
  
    module Induction where
  
      add : ℕ tt → ℕ tt → ℕ tt
      add = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
        (λ u t,c → case ℕT
          (λ t → (c : El (ℕCs t) ℕ u)
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
        (λ u t,c → case ℕT
          (λ t → (c : El (ℕCs t) ℕ u)
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
        (λ m t,c → case VecT
          (λ t → (c : El (VecCs A t) (Vec A) m)
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
        (λ n t,c → case VecT
          (λ t → (c : El (VecCs (Vec A m) t) (Vec (Vec A m)) n)
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
  
    module Eliminator where
  
      elimℕ : (P : (ℕ tt) → Set)
        (pzero : P zero)
        (psuc : (m : ℕ tt) → P m → P (suc m))
        (n : ℕ tt)
        → P n
      elimℕ P pzero psuc = ind ℕD (λ u n → P n)
        (λ u t,c → case ℕT
          (λ t → (c : El (ℕCs t) ℕ u)
                 (ih : Hyps ℕD ℕ (λ u n → P n) u (t , c))
                 → P (con (t , c))
          )
          ( (λ q ih →
              elimEq ⊤ tt (λ u q → P (con (here , q)))
                pzero
                u q
            )
          , (λ n,q ih,tt →
              elimEq ⊤ tt (λ u q → P (con (there here , proj₁ n,q , q)))
                (psuc (proj₁ n,q) (proj₁ ih,tt))
                u (proj₂ n,q)
            )
          , tt
          )
          (proj₁ t,c)
          (proj₂ t,c)
        )
        tt
  
      elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
        (pnil : P zero (nil A))
        (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
        (n : ℕ tt)
        (xs : Vec A n)
        → P n xs
      elimVec A P pnil pcons = ind (VecD A) (λ n xs → P n xs)
        (λ n t,c → case VecT
          (λ t → (c : El (VecCs A t) (Vec A) n)
                 (ih : Hyps (VecD A) (Vec A) (λ n xs → P n xs) n (t , c))
                 → P n (con (t , c))
          )
          ( (λ q ih →
              elimEq (ℕ tt) zero (λ n q → P n (con (here , q)))
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
              elimEq (ℕ tt) (suc n') (λ n q → P n (con (there here , n' , x , xs , q)))
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
      add = elimℕ (λ _ → ℕ tt → ℕ tt)
        (λ n → n)
        (λ m ih n → suc (ih n))
    
      mult : ℕ tt → ℕ tt → ℕ tt
      mult = elimℕ (λ _ → ℕ tt → ℕ tt)
        (λ n → zero)
        (λ m ih n → add n (ih n))
    
      append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
      append A = elimVec A (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
        (λ n ys → ys)
        (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
    
      concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
      concat A m = elimVec (Vec A m) (λ n xss → Vec A (mult n m))
        (nil A)
        (λ n xs xss ih → append A m xs (mult n m) ih)
  
----------------------------------------------------------------------
  
    module GenericEliminator where
  
      add : ℕ tt → ℕ tt → ℕ tt
      add = elim2 ℕTD _
        (λ n → n)
        (λ m ih n → suc (ih n))
        tt
  
      mult : ℕ tt → ℕ tt → ℕ tt
      mult = elim2 ℕTD _
        (λ n → zero)
        (λ m ih n → add n (ih n))
        tt
  
      append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
      append A = elim2 (VecTD A) _
        (λ n ys → ys)
        (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
  
      concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
      concat A m = elim2 (VecTD (Vec A m)) _
        (nil A)
        (λ n xs xss ih → append A m xs (mult n m) ih)
  
----------------------------------------------------------------------

module Levitation where

CasesD : (I : Set) (E : Enum) → Set
CasesD I E = Cases E (λ _ → Desc I)

Args : {I : Set} {E : Enum} (cs : CasesD I E) (t : Tag E) → Desc I
Args = case _ (λ _ → Desc _)

data μ {I : Set} (E : Enum) (cs : CasesD I E) : I → Set where
  con : (t : Tag E) → UncurriedEl (Args cs t) (μ E cs)

-- con2 : {I : Set (E : Enum) (cs : CasesD I E) (t : Tag E)
--   → CurriedEl I (Args I E t cs) (μ I E cs)
-- con2 I E cs t = curryEl I (Args I E t cs) (μ I E cs) (con t)

----------------------------------------------------------------------
