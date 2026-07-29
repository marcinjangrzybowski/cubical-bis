module Cubical.Algebra.OrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
-- to be replaced with fast integers once we have fast rationals
open import Cubical.Data.Int.Fast as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.List hiding ([_])

open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ -- hiding (ℚ₊;max₊;min₊)
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℚOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℚOrderedCommRing = ℚ
0r  (snd ℚOrderedCommRing) = 0
1r  (snd ℚOrderedCommRing) = 1
_+_ (snd ℚOrderedCommRing) = _+ℚ_
_·_ (snd ℚOrderedCommRing) = _·ℚ_
-_  (snd ℚOrderedCommRing) = -ℚ_
_<_ (snd ℚOrderedCommRing) = _<ℚ_
_≤_ (snd ℚOrderedCommRing) = _≤ℚ_
isOrderedCommRing (snd ℚOrderedCommRing) = isOrderedCommRingℚ
  where
  open IsOrderedCommRing

  isOrderedCommRingℚ : IsOrderedCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedCommRingℚ .isCommRing      = ℚCommRing .snd .isCommRing
  isOrderedCommRingℚ .isPseudolattice = ℚ≤Pseudolattice .snd .is-pseudolattice
  isOrderedCommRingℚ .isStrictOrder   = ℚ<StrictOrder .snd .isStrictOrder
  isOrderedCommRingℚ .<-≤-weaken      = <Weaken≤
  isOrderedCommRingℚ .≤≃¬>            = λ x y →
    propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <ℚ x)) (≤→≯ x y) (≮→≥ y x)
  isOrderedCommRingℚ .+MonoR≤         = ≤-+o
  isOrderedCommRingℚ .+MonoR<         = <-+o
  isOrderedCommRingℚ .posSum→pos∨pos  = λ x y → ∣_∣₁ ∘ 0<+ x y
  isOrderedCommRingℚ .<-≤-trans       = isTrans<≤
  isOrderedCommRingℚ .≤-<-trans       = isTrans≤<
  isOrderedCommRingℚ .·MonoR≤         = ≤-·o
  isOrderedCommRingℚ .·MonoR<         = <-·o
  isOrderedCommRingℚ .0<1             = pos<pos tt

module 1/2∈ℚ = Characteristic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)


open Units ℚCommRing
open CommRingTheory ℚCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  ℚCR  = OrderedCommRing→CommRing ℚOrderedCommRing

module PositiveRationals where

  opaque
    0<+Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x +ℚ y
    0<+Closed =
      SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) onFrac
      where
      onFrac : ∀ x y → 0 <ℚ [ x ] → 0 <ℚ [ y ] → 0 <ℚ [ x ] ℚ.+ [ y ]
      onFrac (pos zero , _) (pos _ , _) (pos<pos ())
      onFrac (pos (suc n) , _) (pos zero , _) _ (pos<pos ())
      onFrac (pos (suc n) , _) (pos (suc m) , _) _ _ = pos<pos tt

    0<·Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x ·ℚ y
    0<·Closed =
      SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) onFrac
      where
      onFrac : ∀ x y → 0 <ℚ [ x ] → 0 <ℚ [ y ] → 0 <ℚ [ x ] ℚ.· [ y ]
      onFrac (pos zero , _) (pos _ , _) (pos<pos ())
      onFrac (pos (suc n) , _) (pos zero , _) _ (pos<pos ())
      onFrac (pos (suc n) , _) (pos (suc m) , _) _ _ = pos<pos tt

  open Positive ℚOrderedCommRing 0<+Closed 0<·Closed public renaming (
      R₊ to ℚ₊ ; isSetR₊ to isSetℚ₊ ; R₊≡ to ℚ₊≡
    ; R₊AdditiveSemigroup to +ℚ₊Semigroup ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid)
  open module PositiveHalvesℚ =
    PositiveHalves ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl) 0<+Closed 0<·Closed

  -- Natural number literals for ℚ

  open import Cubical.Data.Nat.Literals public

  instance
    fromNatℚ₊ : HasFromNat ℚ₊
    fromNatℚ₊ = record { Constraint = λ { zero → ⊥ ; _ → Unit }
                       ; fromNat = λ { (suc n) .fst → [ pos (suc n) / 1 ]
                                     ; (suc n) .snd → pos<pos tt } }

  [_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
  [ 1+ n / 1+ m ]₊ = [ pos (suc n) / 1+ m ] , pos<pos tt

  opaque
   0<max : ∀ a b → 0 ℚ.< a → 0 ℚ.< b → 0 ℚ.< ℚ.max a b 
   0<max x y 0<x 0<y =  elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.max a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.max a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      -- NOTE :
      -- if we are only concerned about efficiency, then there is no need to recompute,
      -- as `maxSuc` already reduces efficiently to refl for concrete (large) numbers
      -- however, since `_<_` is an indexed data type, we recompute anyway to avoid
      -- `transpX-_<_` in the normal form
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ maxSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
    x y 0<x 0<y

   
  max₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (max₊ x y) = ℚ.max (fst x) (fst y)
  snd (max₊ x y) = 0<max (fst x) (fst y) (snd x) (snd y)

  max₊LUB< : ∀ δ η ε → δ <₊ ε → η <₊ ε → max₊ δ η <₊ ε
  max₊LUB< δ η ε δ<ε η<ε =
    PT.rec (ℚ.isProp< _ _) proof (ℚ.isTotal≤ ⟨ δ ⟩₊ ⟨ η ⟩₊)
    where
    proof : (δ ≤₊ η) ⊎ (η ≤₊ δ) → max₊ δ η <₊ ε
    proof (inl δ≤η) =
      ℚ.recompute< $
        subst (ℚ._< ⟨ ε ⟩₊) (sym (ℚ.≤→max ⟨ δ ⟩₊ ⟨ η ⟩₊ δ≤η)) η<ε
    proof (inr η≤δ) =
      ℚ.recompute< $ subst (ℚ._< ⟨ ε ⟩₊)
        (sym (ℚ.maxComm ⟨ δ ⟩₊ ⟨ η ⟩₊
          ∙ ℚ.≤→max ⟨ η ⟩₊ ⟨ δ ⟩₊ η≤δ))
        δ<ε

  opaque
   0<min : ∀ a b → 0 ℚ.< a → 0 ℚ.< b → 0 ℚ.< ℚ.min a b 
   0<min x y 0<x 0<y = elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.min a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.min a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ minSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
      x y 0<x 0<y


  min₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (min₊ x y) = ℚ.min (fst x) (fst y)
  snd (min₊ x y) = 0<min (fst x) (fst y) (snd x) (snd y) 

  min₊≤L : ∀ ε δ → min₊ ε δ ≤₊ ε
  min₊≤L ε δ = min≤ ⟨ ε ⟩₊ ⟨ δ ⟩₊

  min₊≤R : ∀ ε δ → min₊ ε δ ≤₊ δ
  min₊≤R ε δ = ℚ.recompute≤ $
    subst (_≤ℚ ⟨ δ ⟩₊) (ℚ.minComm ⟨ δ ⟩₊ ⟨ ε ⟩₊) (min≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊)

  min/2₊<L : ∀ ε δ → (min₊ ε δ /2₊) <₊ ε
  min/2₊<L ε δ = begin<
    ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
    ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤L ε δ ⟩
    ⟨ ε ⟩₊            ◾

  min/2₊<R : ∀ ε δ → (min₊ ε δ /2₊) <₊ δ
  min/2₊<R ε δ = begin<
    ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
    ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤R ε δ ⟩
    ⟨ δ ⟩₊            ◾

  ≤ℤ→≤ℚ : ∀ m n → m ℤ.≤ n → [ m , 1 ] ≤ℚ [ n , 1 ]
  ≤ℤ→≤ℚ m n = inj ∘S (subst2 ℤ._≤_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n)))

  <ℤ→<ℚ : ∀ m n → m ℤ.< n → [ m , 1 ] <ℚ [ n , 1 ]
  <ℤ→<ℚ m n = inj ∘S subst2 ℤ._<_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n))


  [k/n]<[k'/n] : ∀ k k' n → k ℤ.< k' → ([ ( k , n ) ]) <ℚ ([ (k' , n) ])
  [k/n]<[k'/n] k k' n k<k' = inj (ℤ.<-·o {k} k<k')

  [k/n]≤[k'/n] : ∀ k k' n → k ℤ.≤ k' → ([ ( k , n ) ]) ≤ℚ ([ (k' , n) ])
  [k/n]≤[k'/n] k k' n k<k' = inj (ℤ.≤-·o {k} k<k')

  0<[k/n]→0<k : ∀ k n → 0 <ℚ [ k / n  ] → 0 ℤ.< k
  0<[k/n]→0<k (pos zero) _ (pos<pos ())
  0<[k/n]→0<k (pos (suc _)) _ _ = ℤ.pos<pos tt
  
  eqElim₊ : (lrhs : ℚ₊ → ℚ × ℚ) →
    (∀ {k m} → fst (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt)))
          ≡  snd (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))))
      → ∀ (ε : ℚ₊) → fst (lrhs ε) ≡ snd (lrhs ε)
  eqElim₊ lrhs p = uncurry (ElimProp.go w)
    where
    w : ElimProp (λ z → ∀ p →  fst (lrhs (z , p)) ≡ snd (lrhs (z , p)))
    w .ElimProp.isPropB _ = isPropΠ λ _ → isSetℚ _ _
    w .ElimProp.f (ℤ.pos (suc n) , (1+ n₁)) (inj (ℤ.pos<pos _)) = p {n} {n₁}

  private
   substℚ₊ : ∀ {ℓ} (A : ℚ → Type ℓ) (lrhs : ℚ₊ → ℚ × ℚ) →
     (∀ {k m} → fst (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt)))
           ≡  snd (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))))
       → ∀ (ε : ℚ₊) → A (fst (lrhs ε)) → A (snd (lrhs ε))
   substℚ₊ A lrhs p ε =
     subst A (eqElim₊ lrhs p ε)


  eqElim₂₊ : {lhs rhs : ℚ₊ → ℚ₊ → ℚ} →
    (∀ k m k' m' → lhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))
            ([ ((ℤ.pos (suc k')) , 1+ m') ] , inj (ℤ.pos<pos tt))
          ≡  rhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))
           ([ ((ℤ.pos (suc k')) , 1+ m') ] , inj (ℤ.pos<pos tt)))
      → ∀ {ε ε' : ℚ₊} → lhs ε ε' ≡ rhs ε ε'
  eqElim₂₊ {lhs} {rhs} p {ε , 0<ε} {ε' , 0<ε'} = ElimProp2.go w ε ε' 0<ε 0<ε'
    where
    w : ElimProp2 (λ z z' → ∀ p p' →  lhs (z , p) (z' , p') ≡ rhs (z , p) (z' , p'))
    w .ElimProp2.isPropB _ _ = isPropΠ2 λ _ _ → isSetℚ _ _
    w .ElimProp2.f (ℤ.pos (suc n) , (1+ n₁)) (ℤ.pos (suc m) , (1+ m₁)) (inj (ℤ.pos<pos _)) (inj (ℤ.pos<pos _)) =
      p n n₁ m m₁


  module EqElims where
   data ℚTypes : Type where
    [ℚ] [ℚ₊] : ℚTypes

   ℚSignature : Type
   ℚSignature = List ℚTypes

   lrhsDom : ℚTypes → Type
   lrhsDom [ℚ] = ℚ
   lrhsDom [ℚ₊] = ℚ₊


   lrhsDomFst : ℚTypes → Type
   lrhsDomFst [ℚ] = ℤ
   lrhsDomFst [ℚ₊] = ℕ₊₁

   lrhsCtr : ∀ b → lrhsDomFst b → ℕ₊₁ → (lrhsDom b)
   lrhsCtr [ℚ] k m = [ k , m ]
   lrhsCtr [ℚ₊] n m = [ ℕ₊₁→ℤ n , m ] , inj (ℤ.pos<pos tt)

   LRhs : ℚSignature → Type
   LRhs [] = ℚ × ℚ
   LRhs (x ∷ xs) = lrhsDom x → LRhs xs

   LemType : ∀ s → LRhs s → Type
   LemType [] (lhs , rhs) = lhs ≡ rhs
   LemType (x ∷ xs) lrhs = (k : lrhsDomFst x) (m : ℕ₊₁) → LemType xs (lrhs (lrhsCtr x k m))


   EqType : ∀ s → LRhs s → Type
   EqType [] (lhs , rhs) = lhs ≡ rhs
   EqType (x ∷ xs) lrhs = (q : lrhsDom x) → EqType xs (lrhs q)

   isPropEqType : ∀ s → (lrhs : LRhs s) → isProp (EqType s lrhs)
   isPropEqType [] lrhs = isSetℚ _ _
   isPropEqType (_ ∷ s) lrhs = isPropΠ $ isPropEqType s ∘ lrhs

   EllimEqₛ : ∀ s → (lrhs : LRhs s) → LemType s lrhs → EqType s lrhs
   EllimEqₛ [] lrhs e = e
   EllimEqₛ ([ℚ] ∷ xs) lrhs e = ElimProp.go w
    where
    w : ElimProp _
    w .ElimProp.isPropB = isPropEqType xs ∘ lrhs
    w .ElimProp.f (k , m) = EllimEqₛ xs (lrhs _) (e k m)

   EllimEqₛ ([ℚ₊] ∷ xs) lrhs e = uncurry (ElimProp.go w)
    where
    w : ElimProp (λ z → ∀ p → EqType xs (lrhs (z , p)))
    w .ElimProp.isPropB q = isPropΠ λ _ → isPropEqType xs (lrhs (q , _))
    w .ElimProp.f (ℤ.pos (suc n) , m) (inj (ℤ.pos<pos _)) = EllimEqₛ xs (lrhs _) (e (1+ n) m)

module NonNegativeRationals where


  opaque
    0≤+Closed : ∀ x y → 0 ≤ℚ x → 0 ≤ℚ y → 0 ≤ℚ x +ℚ y
    0≤+Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp≤ 0 _)))
     λ
      { (pos _ , _) (pos _ , _) (pos≤pos _) (pos≤pos _) → pos≤pos _ }

    0≤·Closed : ∀ x y → 0 ≤ℚ x → 0 ≤ℚ y → 0 ≤ℚ x ·ℚ y
    0≤·Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp≤ 0 _))) λ
      { (pos _ , _) (pos _ , _) (pos≤pos _) (pos≤pos _) → pos≤pos _   }

  open NonNegative ℚOrderedCommRing 0≤+Closed 0≤·Closed public renaming (
      R₀₊ to ℚ₀₊ ; isSetR₀₊ to isSetℚ₀₊ ; R₀₊≡ to ℚ₀₊≡
    ; R₀₊CommSemiring to +ℚ₀₊CommSemiring)


  instance
    fromNatℚ₀₊ : HasFromNat ℚ₀₊
    fromNatℚ₀₊ = record { Constraint = λ _ → Unit
                       ; fromNat = λ n → ([ pos n / 1 ] , pos≤pos _) }
