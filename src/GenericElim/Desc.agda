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
  → UncurriedBranches E P X → CurriedBranches E P X
curryBranches {[]} f = f tt
curryBranches {l ∷ E} f = λ c → curryBranches (λ cs → f (c , cs))

uncurryBranches : {E : Enum} {P : Tag E → Set} {X : Set}
  → CurriedBranches E P X → UncurriedBranches E P X
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
UncurriedEl D X = ∀{i} → El D X i → X i

CurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedEl (End i) X = X i
CurriedEl (Rec i D) X = (x : X i) → CurriedEl D X
CurriedEl (Arg A B) X = (a : A) → CurriedEl (B a) X
CurriedEl (RecFun A B D) X = ((a : A) → X (B a)) → CurriedEl D X

CurriedEl' : {I : Set} (D : Desc I) (X : ISet I) (i : I) → Set
CurriedEl' (End j) X i = j ≡ i → X i
CurriedEl' (Rec j D) X i = (x : X j) → CurriedEl' D X i
CurriedEl' (Arg A B) X i = (a : A) → CurriedEl' (B a) X i
CurriedEl' (RecFun A B D) X i = ((a : A) → X (B a)) → CurriedEl' D X i

curryEl : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedEl D X → CurriedEl D X
curryEl (End i) X cn = cn refl
curryEl (Rec i D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A B) X cn = λ a → curryEl (B a) X (λ xs → cn (a , xs))
curryEl (RecFun A B D) X cn = λ f → curryEl D X (λ xs → cn (f , xs))

uncurryEl : {I : Set} (D : Desc I) (X : ISet I)
  → CurriedEl D X → UncurriedEl D X
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
  ∀ i (xs : El D X i) (ihs : Hyps D X P i xs) → P i (cn xs)

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

CurriedHyps' : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (i : I)
  (cn : El D X i → X i)
  → Set
CurriedHyps' (End j) X P i cn = (q : j ≡ i) → P i (cn q)
CurriedHyps' (Rec j D) X P i cn =
  (x : X j) → P j x → CurriedHyps' D X P i (λ xs → cn (x , xs))
CurriedHyps' (Arg A B) X P i cn =
  (a : A) → CurriedHyps' (B a) X P i (λ xs → cn (a , xs))
CurriedHyps' (RecFun A B D) X P i cn =
  (f : (a : A) → X (B a)) (ihf : (a : A) → P (B a) (f a)) → CurriedHyps' D X P i (λ xs → cn (f , xs))

curryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → UncurriedHyps D X P cn
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
  → CurriedHyps D X P cn
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

data μ {I : Set} (D : Desc I) : ISet I where
  init : UncurriedEl D (μ D)

inj : {I : Set} (D : Desc I) → CurriedEl D (μ D)
inj D = curryEl D (μ D) init

----------------------------------------------------------------------

ind :
  {I : Set}
  (D : Desc I)
  (P : (i : I) → μ D i → Set)
  (α : UncurriedHyps D (μ D) P init)
  (i : I)
  (x : μ D i)
  → P i x

hyps :
  {I : Set}
  (D₁ : Desc I)
  (P : (i : I) → μ D₁ i → Set)
  (α : UncurriedHyps D₁ (μ D₁) P init)
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

indCurried : {I : Set} (D : Desc I)
  (P : (i : I) → μ D i → Set)
  (f : CurriedHyps D (μ D) P init)
  (i : I)
  (x : μ D i)
  → P i x
indCurried D P f i x = ind D P (uncurryHyps D (μ D) P init f) i x

Summer : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (X  : ISet I) (cn : UncurriedEl D X)
  (P : (i : I) → X i → Set)
  → Tag E → Set
Summer E C X cn P t =
  let D = Arg (Tag E) C in
  CurriedHyps (C t) X P (λ xs → cn (t , xs))

SumCurriedHyps : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  → Tag E → Set
SumCurriedHyps E C P t =
  let D = Arg (Tag E) C in
  Summer E C (μ D) init P t

elimUncurried : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  → Branches E (SumCurriedHyps E C P)
  → (i : I) (x : μ D i) → P i x
elimUncurried E C P cs i x =
  let D = Arg (Tag E) C in
  indCurried D P
    (case (SumCurriedHyps E C P) cs)
    i x

elim : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  → CurriedBranches E
      (SumCurriedHyps E C P)
      ((i : I) (x : μ D i) → P i x)
elim E C P = curryBranches (elimUncurried E C P)

----------------------------------------------------------------------

Soundness : Set
Soundness = {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  (cs : Branches E (SumCurriedHyps E C P))
  (i : I) (x : μ D i)
  → ∃ λ α
  → elimUncurried E C P cs i x ≡ ind D P α i x

sound : Soundness
sound E C P cs i x =
  let D = Arg (Tag E) C in
  (uncurryHyps D (μ D) P init (case (SumCurriedHyps E C P) cs)) , refl

Completeness : Set
Completeness = {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  (α : UncurriedHyps D (μ D) P init)
  (i : I) (x : μ D i)
  → ∃ λ cs
  → ind D P α i x ≡ elimUncurried E C P cs i x

postulate undefinedForRecFun : {A : Set} → A

uncurryHypsIdent : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (α : UncurriedHyps D X P cn)
  (i : I) (xs : El D X i) (ihs : Hyps D X P i xs)
  → α i xs ihs ≡ uncurryHyps D X P cn (curryHyps D X P cn α) i xs ihs
uncurryHypsIdent (End .i) X P cn α i refl tt = refl
uncurryHypsIdent (Rec j D) X P cn α i (x , xs) (p , ps) =
  uncurryHypsIdent D X P (λ xs → cn (x , xs)) (λ k ys rs → α k (x , ys) (p , rs)) i xs ps
uncurryHypsIdent (Arg A B) X P cn α i (a , xs) ps =
  uncurryHypsIdent (B a) X P (λ xs → cn (a , xs)) (λ j ys → α j (a , ys)) i xs ps
uncurryHypsIdent (RecFun A B D) X P cn α i xs ihs = undefinedForRecFun

postulate
  ext3 : {A : Set} {B : A → Set} {C : (a : A) → B a → Set} {Z : (a : A) (b : B a) → C a b → Set}
    (f g : (a : A) (b : B a) (c : C a b) → Z a b c)
    → ((a : A) (b : B a) (c : C a b) → f a b c ≡ g a b c)
    → f ≡ g

toBranches : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (X  : ISet I) (cn : UncurriedEl D X)
  (P : (i : I) → X i → Set)
  (α : UncurriedHyps D X P cn)
  → Branches E (Summer E C X cn P)
toBranches [] C X cn P α = tt
toBranches (l ∷ E) C X cn P α =
    curryHyps (C here) X P (λ xs → cn (here , xs)) (λ i xs → α i (here , xs))
  , toBranches E (λ t → C (there t)) X
     (λ xs → cn (there (proj₁ xs) , proj₂ xs))
     P (λ i xs ih → α i (there (proj₁ xs) , proj₂ xs) ih)

ToBranches : {I : Set} {E : Enum} (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (X  : ISet I) (cn : UncurriedEl D X)
  (P : (i : I) → X i → Set)
  (α : UncurriedHyps D X P cn)
  (t : Tag E)
  → let β = toBranches E C X cn P α in
  case (Summer E C X cn P) β t ≡ curryHyps D X P cn α t
ToBranches C X cn P α here = refl
ToBranches C X cn P α (there t)
  with ToBranches (λ t → C (there t)) X
    (λ xs → cn (there (proj₁ xs) , proj₂ xs))
    P (λ i xs ih → α i (there (proj₁ xs) , proj₂ xs) ih) t
... | ih rewrite ih = refl

completeα : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  (α : UncurriedHyps D (μ D) P init)
  (i : I) (xs : El D (μ D) i) (ihs : Hyps D (μ D) P i xs)
  → let β = toBranches E C (μ D) init P α in
  α i xs ihs ≡ uncurryHyps D (μ D) P init (case (SumCurriedHyps E C P) β) i xs ihs
completeα E C P α i (t , xs) ihs
  with ToBranches C (μ D) init P α t where D = Arg (Tag E) C
... | q rewrite q = uncurryHypsIdent D (μ D) P init α i (t , xs) ihs where D = Arg (Tag E) C

complete' : {I : Set} (E : Enum) (C : Tag E → Desc I)
  → let D = Arg (Tag E) C in
  (P : (i : I) → μ D i → Set)
  (α : UncurriedHyps D (μ D) P init)
  (i : I) (x : μ D i)
  → let β = toBranches E C (μ D) init P α in
  ind D P α i x ≡ elimUncurried E C P β i x
complete' E C P α i (init (t , xs)) = cong
  (λ f → ind D P f i (init (t , xs)))
  (ext3 α
    (uncurryHyps D (μ D) P init (case (SumCurriedHyps E C P) β)) 
    (completeα E C P α))
  where
  D = Arg (Tag E) C 
  β = toBranches E C (μ D) init P α

complete : Completeness
complete E C P α i x =
  let D = Arg (Tag E) C in
    toBranches E C (μ D) init P α
  , complete' E C P α i x

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

  nilD : (A : Set) → Desc (ℕ tt)
  nilD A = End zero

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

  NilEl : (A : Set) (n : ℕ tt) → Set
  NilEl A n = El (nilD A) (Vec A) n

  ConsEl : (A : Set) → ℕ tt → Set
  ConsEl A n = El (consD A) (Vec A) n

  VecEl : (A : Set) → ℕ tt → Set
  VecEl A n = El (VecD A) (Vec A) n

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

  ℕE : Enum
  ℕE = "zero" ∷ "suc" ∷ []

  VecE : Enum
  VecE = "nil" ∷ "cons" ∷ []

  ℕT : Set
  ℕT = Tag ℕE

  VecT : Set
  VecT = Tag VecE

  zeroT : ℕT
  zeroT = here

  sucT : ℕT
  sucT = there here

  nilT : VecT
  nilT = here

  consT : VecT
  consT = there here

  ℕC : ℕT → Desc ⊤
  ℕC = caseD $
      End tt
    , Rec tt (End tt)
    , tt

  ℕD : Desc ⊤
  ℕD = Arg ℕT ℕC

  ℕ : ⊤ → Set
  ℕ = μ ℕD

  zero : ℕ tt
  zero = init (zeroT , refl)

  suc : ℕ tt → ℕ tt
  suc n = init (sucT , n , refl)

  VecC : (A : Set) → VecT → Desc (ℕ tt)
  VecC A = caseD $
      End zero
    , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
    , tt

  nilD : (A : Set) → Desc (ℕ tt)
  nilD A = End zero

  consD : (A : Set) → Desc (ℕ tt)
  consD A = Arg (ℕ tt) (λ n → Arg A (λ _ → Rec n (End (suc n))))

  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = Arg VecT (VecC A)

  Vec : (A : Set) → ℕ tt → Set
  Vec A = μ (VecD A)

  NilEl : (A : Set) (n : ℕ tt) → Set
  NilEl A n = El (nilD A) (Vec A) n

  ConsEl : (A : Set) → ℕ tt → Set
  ConsEl A n = El (consD A) (Vec A) n

  VecEl : (A : Set) → ℕ tt → Set
  VecEl A n = El (VecD A) (Vec A) n

  NilHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : NilEl A n) → Set
  NilHyps A P n xs = Hyps (nilD A) (Vec A) P n xs

  ConsHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : ConsEl A n) → Set
  ConsHyps A P n xs = Hyps (consD A) (Vec A) P n xs

  VecHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : VecEl A n) → Set
  VecHyps A P n xs = Hyps (VecD A) (Vec A) P n xs

  ConsUncurriedHyps : (A : Set)
    (P : (n : ℕ tt) → Vec A n → Set)
    (cn : UncurriedEl (consD A) (Vec A)) → Set
  ConsUncurriedHyps A P cn = UncurriedHyps (consD A) (Vec A) P cn

  nil : (A : Set) → Vec A zero
  nil A = init (nilT , refl)

  cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons A n x xs = init (consT , n , x , xs , refl)
 
  nil2 : (A : Set) → Vec A zero
  nil2 A = inj (VecD A) nilT

  cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons2 A = inj (VecD A) consT

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

    Concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Set
    Concat A m n xss = Vec A (mult n m)

    ConsBranch : (A : Set) (m : ℕ tt)
      → Set
    ConsBranch A m = UncurriedHyps (consD (Vec A m)) (Vec (Vec A m)) (Concat A m)
      (λ xs → init (consT , xs))

    ConsElimBranch : (A : Set) (m : ℕ tt)
      → Set
    ConsElimBranch A m = CurriedHyps (consD (Vec A m)) (Vec (Vec A m)) (Concat A m)
      (λ xs → init (consT , xs))

    ElimBranch : (t : VecT) (A : Set) (m : ℕ tt)
      → Set
    ElimBranch t A m = SumCurriedHyps VecE (VecC (Vec A m)) (Concat A m) t

    nilBranch : (A : Set) (m n : ℕ tt)
      (xss : NilEl (Vec A m) n)
      (ihs : NilHyps (Vec A m) (Concat A m) n xss)
      → Vec A (mult n m)
    nilBranch A m n q u = subst
      (λ n → Vec A (mult n m))
      q (nil A)

    consBranch : (A : Set) (m : ℕ tt)
      → ConsBranch A m
      -- (xss : ConsEl (Vec A m) n)
      -- (ihs : ConsHyps (Vec A m) (Concat A m) n xss)
      -- → Vec A (mult n m)
    consBranch A m n n',xs,xss,q ih,u =
      let n' = proj₁ n',xs,xss,q
          xs = proj₁ (proj₂ n',xs,xss,q)
          q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
          ih = proj₁ ih,u
      in subst
        (λ n → Vec A (mult n m))
        q (append A m xs (mult n' m) ih)

    ConcatConvoy : (A : Set) (m n : ℕ tt) (t : VecT) → Set
    ConcatConvoy A m n t =
      (xss : El (VecC (Vec A m) t) (Vec (Vec A m)) n)
      (ihs : VecHyps (Vec A m) (Concat A m) n (t , xss))
      → Vec A (mult n m)

    concatα : (A : Set) (m n : ℕ tt)
      (xss : VecEl (Vec A m) n)
      (ihs : VecHyps (Vec A m) (Concat A m) n xss)
      → Vec A (mult n m)
    concatα A m n xss = case (ConcatConvoy A m n)
      (nilBranch A m n , consBranch A m n , tt)
      (proj₁ xss)
      (proj₂ xss)

    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Concat A m n xss
    concat A m = ind
      (VecD (Vec A m))
      (Concat A m)
      (concatα A m)

----------------------------------------------------------------------

  module ElimUncurried where

    elimℕ : (P : (ℕ tt) → Set)
      (pzero : P zero)
      (psuc : (m : ℕ tt) → P m → P (suc m))
      (n : ℕ tt)
      → P n
    elimℕ P pzero psuc = ind ℕD (λ u n → P n)
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

    elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
      (pnil : P zero (nil A))
      (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
      (n : ℕ tt)
      (xs : Vec A n)
      → P n xs
    elimVec A P pnil pcons = ind (VecD A) (λ n xs → P n xs)
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

  module GenericElimUncurried where

    add : ℕ tt → ℕ tt → ℕ tt
    add = elim ℕE ℕC _
      (λ n → n)
      (λ m ih n → suc (ih n))
      tt

    mult : ℕ tt → ℕ tt → ℕ tt
    mult = elim ℕE ℕC _
      (λ n → zero)
      (λ m ih n → add n (ih n))
      tt

    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
    append A = elim VecE (VecC A) _
      (λ n ys → ys)
      (λ m x xs ih n ys → cons A (add m n) x (ih n ys))

    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = elim VecE (VecC (Vec A m)) (λ n xss → Vec A (mult n m))
      (nil A)
      (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
