module Cubical.Data.Rationals.Order.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ;pos;negsuc;ℕ₊₁→ℤ)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Int.Fast.Properties as ℤ using ()
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Int.Fast.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero;znots)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.Rationals.Order

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Foundations.Powerset


open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection
import Cubical.Tactics.CommRingSolver.Imports as 𝓢
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals


open PositiveRationals
open NonNegativeRationals
open PositiveHalvesℚ

open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)
open import Cubical.Data.Rationals.Order.AbsoluteValue

private
  module ℚClamp = OrderedCommRingClamp ℚOrderedCommRing

maxNeg≡negMin : ∀ x y → max (- x) (- y) ≡ - (min x y)
maxNeg≡negMin = joinNeg≡negMeet

≤→<+₊ : ∀ x y (ε : ℚ₊) → x ≤ y → x < y + fst ε
≤→<+₊ x y ε x≤y =
  subst (λ z → z < y + fst ε) (+IdR x)
    (≤<Monotone+ x y 0 (fst ε) x≤y (snd ε))

elimBy≡⊎<' : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x → A x x)
  → (∀ x (ε : ℚ₊) → A x (x + fst ε))
  → ∀ x y → A x y
elimBy≡⊎<' {A = A} s r f' =
 elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)

 where
 f : ∀ x y → x < y → A x y
 f x y v = subst (A x) ℚ!! $ f' x (y - x , <≤ℚ![ v ])


+MaxDistrℚ : ∀ x y z → (max x y) + z ≡ max (x + z) (y + z)
+MaxDistrℚ = ℚClamp.+DistR⊔

+MinDistrℚ : ∀ x y z → (min x y) + z ≡ min (x + z) (y + z)
+MinDistrℚ = ℚClamp.+DistR⊓


<MonotoneMax : ∀ m o n s → m < n → o < s → max m o < max n s
<MonotoneMax =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (maxComm x y) (maxComm s o)
                 ((X s o) v u))
   λ x y x≤y n s _ y<s →
     subst (_< max n s) (sym (≤→max x y x≤y))
      (isTrans<≤ _ _ _ y<s (≤max' n s))

<MonotoneMin : ∀ n s m o  → m < n → o < s → min m o < min n s
<MonotoneMin =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (minComm s o) (minComm x y)
                 ((X s o) v u))
   λ x y x≤y n s n<x _ →
     subst (min n s <_) (sym (≤→min x y x≤y))
       (isTrans≤< _ _ _ (min≤ n s) n<x)


clampDelta : ∀ L L' x → clamp L L' x ≡
               (x + clamp (L - x) (L' - x) 0)
clampDelta = ℚClamp.clampDelta


clampDiff : ∀ L L' x y → x ≤ y →
    clamp L L' y - clamp L L' x ≤ y - x
clampDiff = ℚClamp.clampDiff


minDiff : ∀ L' x y → x ≤ y →
    min y L' - min x L' ≤ y - x
minDiff L' x y x≤y =
 subst (_≤ (y - x))
    (cong₂ _-_
     (cong (flip min L') (≤→max x y x≤y ))
     (cong (flip min L') (maxIdem x)))
     (clampDiff x L' x y x≤y)


clampDist' : ∀ L L' x y → x ≤ y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist' L L' x y _ = ℚClamp.clampDist L L' x y

clampDist : ∀ L L' x y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist = ℚClamp.clampDist

maxDist : ∀ M x y →
    abs (max M y - max M x) ≤ abs (y - x)
maxDist M x y =
  subst2 {x = min (max M y) (max M (max x y))}
          {(max M y)}
    {z = min (max M x) (max M (max x y))} {(max M x)}
    (λ a b → abs (a - b) ≤ abs (y - x))
    (≤→min _ _ (subst (max M y ≤_)
      (sym (maxAssoc M y x) ∙ cong (max M) (maxComm y x))
      (≤max _ x)))
    (≤→min _ _
      ((subst (max M x ≤_)
      (sym (maxAssoc M x y))
      (≤max _ y))))
    (clampDist M (max M (max x y)) x y)


≤→<⊎≡ : ∀ p q → p ≤ q → (p ≡ q) ⊎ (p < q)
≤→<⊎≡ p q x with p ≟ q
... | lt x₁ = inr x₁
... | eq x₁ = inl x₁
... | gt x₁ = ⊥.rec $ ≤→≯ p q x x₁


·MaxDistrℚ : ∀ x y z → 0< z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ = SQ.elimProp3 (λ _ _ _ → isPropΠ λ _ → isSetℚ _ _)
  www

 where
 www : (a b c : ℤ.ℤ × ℕ₊₁) →
         0< _//_.[ c ] →
         max _//_.[ a ] _//_.[ b ] · _//_.[ c ] ≡
         max (_//_.[ a ] · _//_.[ c ]) (_//_.[ b ] · _//_.[ c ])
 www (a , a') (b , b') (c@(pos (suc n)) , c') (inj (ℤ.pos<pos x)) = eq/ _ _ wwww
  where


   wwww : ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· c
            ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c' ·₊₁ (b' ·₊₁ c'))
          ≡ ℤ.max ((a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b' ·₊₁ c'))
                    ((b ℤ.· c) ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c'))  ℤ.·
              ℕ₊₁→ℤ (a' ·₊₁ b' ·₊₁ c')
   wwww =
    cong (ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n) ℤ.·_)
      (cong (λ ac → ℕ₊₁→ℤ (ac ·₊₁ (b' ·₊₁ c'))) (·₊₁-comm a'  c')
       ∙∙ cong ℕ₊₁→ℤ (sym (·₊₁-assoc c' a' (b' ·₊₁ c'))) ∙∙
         ℤ.pos·pos (suc (c' .ℕ₊₁.n)) (ℕ₊₁→ℕ (a' ·₊₁ (b' ·₊₁ c'))))
      ∙∙ ℤ! ∙∙
    cong₂ (ℤ._·_)
       (cong (ℤ._· (pos (ℕ₊₁→ℕ c')))
         (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') (suc n))
         ∙ ℤ.·DistPosLMax
              ((a ℤ.· ℕ₊₁→ℤ b') ℤ.· pos (suc n))
              ((b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n)) (ℕ₊₁→ℕ c')
          ∙ cong₂ ℤ.max ℤ! ℤ!)
           (cong ℕ₊₁→ℤ (·₊₁-assoc a' b' c'))


·MaxDistrℚ' : ∀ x y z → 0 ≤ z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ' x y z =
  ⊎.rec (λ p → cong ((max x y) ·_) (sym p) ∙
        ·AnnihilR (max x y)  ∙ cong₂ max (sym (·AnnihilR x) ∙ cong (x ·_) p)
            (sym (·AnnihilR y) ∙ cong (y ·_) p))
    (·MaxDistrℚ x y z) ∘ (≤→≡⊎< 0 z)

≤Monotone·-onNonNeg : ∀ x x' y y' →
  x ≤ x' →
  y ≤ y' →
  0 ≤ x →
  0 ≤ y →
   x · y ≤ x' · y'
≤Monotone·-onNonNeg x x' y y' x≤x' y≤y' 0≤x 0≤y =
  isTrans≤ _ _ _ (≤-·o x x' y 0≤y x≤x')
   (≤-o· y y' x' (isTrans≤ 0 _ _ 0≤x x≤x') y≤y')

<Monotone·-onPos : ∀ x x' y y' →
  x < x' →
  y < y' →
  0 ≤ x →
  0 ≤ y →
   x · y < x' · y'
<Monotone·-onPos x x' y y' x₁ x₂ x₃ x₄ =
   let zz = 0<-m·n (x' - x) (y' - y) (-< x x' x₁) (-< y y' x₂)
   in subst2 _<_ (+IdL _ ∙ +IdR _)
          (ℚ!!)
        (<≤Monotone+ 0 ((x' - x) · (y' - y)) (x · y + 0)
             (x' · y + ((x · (y' - y)))) zz
               (≤Monotone+ (x · y) (x' · y) 0  (x · (y' - y))
                (≤-·o x x' y x₄ (<Weaken≤ x x' x₁))
                (subst (_≤ x · (y' - y))
                  (·AnnihilL (y' - y)) $ ≤-·o 0 x (y' - y)
                  (<Weaken≤ 0 (y' - y) (-< y y' x₂) ) x₃)))


≤<Monotone·-onPos : ∀ x x' y y' →
  x ≤ x' →
  y < y' →
  0 < x →
  0 ≤ y →
   x · y < x' · y'
≤<Monotone·-onPos x x' y y' x≤x' y<y' 0<x 0≤y =
  isTrans≤< _ _ _
    (≤-·o x x' y 0≤y x≤x')
    (<-o· y y' x' (isTrans<≤ 0 _ _ 0<x x≤x') y<y')

maxWithPos : ℚ₊ → ℚ → ℚ₊
maxWithPos ε q .fst = max (fst ε) q
maxWithPos ε q .snd = 
 (isTrans<≤ 0 (fst ε) _ (snd ε) (≤max (fst ε) q))


clam∈ℚintervalℙ : ∀ a b → (a ≤ b) → ∀ x → clamp a b x ∈ ℚintervalℙ a b
clam∈ℚintervalℙ a b a≤b x = ≤clamp _ _ _ a≤b , (clamp≤ a _ x)

∈ℚintervalℙ→clam≡ : ∀ a b → ∀ x →
    x ∈ ℚintervalℙ a b → x ≡ clamp a b x
∈ℚintervalℙ→clam≡ a b x = sym ∘ uncurry (inClamps a b x)


clamp-contained-agree : ∀ (a b a' b' x : ℚ)
  → a ≤ a'
  → b' ≤ b
  → x ∈ ℚintervalℙ a' b'
  → clamp a b x ≡ clamp a' b' x
clamp-contained-agree a b a' b' x a≤a' b'≤b x∈ =
  sym (∈ℚintervalℙ→clam≡ a b x
   ((isTrans≤ _ _ _ a≤a' (fst x∈)) ,
    (isTrans≤ _ _ _ (snd x∈) b'≤b))) ∙ ∈ℚintervalℙ→clam≡ a' b' x x∈

module Exponentiationℚ =
  Exponentiation ℚCommRing renaming (_^_ to _^ⁿ_) 

open Exponentiationℚ using (_^ⁿ_) public 

0<ℚ^ⁿ : ∀ q (0<q : 0< q) n → 0< (q ^ⁿ n)
0<ℚ^ⁿ q 0<q zero = inj (ℤ.pos<pos tt)
0<ℚ^ⁿ q 0<q (suc n) = snd ((q , 0<q) ·₊  ((q ^ⁿ n) , 0<ℚ^ⁿ q 0<q n))

0≤ℚ^ⁿ : ∀ q (0≤q : 0 ≤ q) n → 0 ≤ (q ^ⁿ n)
0≤ℚ^ⁿ q 0≤q zero = 𝟚.toWitness {Q = ≤Dec 0 1} tt
0≤ℚ^ⁿ q 0≤q (suc n) = ≤Monotone·-onNonNeg
 0 _ 0 _
  0≤q (0≤ℚ^ⁿ q 0≤q n)
    (isRefl≤ 0) (isRefl≤ 0)


x^ⁿ≤1 : ∀ x n → 0 ≤ x → x ≤ 1 →  (x ^ⁿ n) ≤ 1
x^ⁿ≤1 x zero 0≤x x≤1 = isRefl≤ 1
x^ⁿ≤1 x (suc n) 0≤x x≤1 =
 ≤Monotone·-onNonNeg _ 1 _ 1
   x≤1 (x^ⁿ≤1 x n 0≤x x≤1)   0≤x (0≤ℚ^ⁿ x 0≤x n)

1≤x^ⁿ : ∀ x n → 1 ≤ x →  1 ≤ (x ^ⁿ n)
1≤x^ⁿ x zero 1≤x = isRefl≤ 1
1≤x^ⁿ x (suc n) 1≤x =
 ≤Monotone·-onNonNeg 1 _ 1 _
  1≤x (1≤x^ⁿ x n 1≤x) decℚ≤? decℚ≤?

1<x^ⁿ : ∀ x n → 1 < x →  1 < (x ^ⁿ (suc n))
1<x^ⁿ x zero 1<x = subst (1 <_) ℚ!! 1<x
1<x^ⁿ x (suc n) 1<x =
 <Monotone·-onPos 1 _ 1 _ 
   1<x (1<x^ⁿ x n 1<x)    (decℚ≤? {0} {1})
     (decℚ≤? {0} {1})


_ℚ₊^ⁿ_ : ℚ₊ → ℕ → ℚ₊
(q , 0<q) ℚ₊^ⁿ n = (q ^ⁿ n) , 0<ℚ^ⁿ q 0<q n


fromNat-^ : ∀ m n → ((fromNat m) ^ⁿ n ) ≡ fromNat (m ℕ.^ n)
fromNat-^ m ℕ.zero = refl
fromNat-^ m (suc n) =   
 cong ((fromNat m) ·_) (fromNat-^ m n) ∙
   ℕ·→ℚ· m (m ℕ.^ n)

-1ⁿ : ℕ → ℚ
-1ⁿ = ℚR.alternatingSign

abs[-1ⁿ]≡1 : ∀ n → abs (-1ⁿ n) ≡ 1
abs[-1ⁿ]≡1 = abs-alternatingSign

-1ⁿ· : ℕ → ℚ → ℚ
-1ⁿ· = ℚR.alternate

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ - (-1ⁿ· n x)
-1ⁿ·-suc = ℚR.alternate-suc

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 = ℚR.alternate-even

-1ⁿ-suc : ∀ n →  (-1ⁿ (suc n)) ≡ - ((-1ⁿ n))
-1ⁿ-suc = ℚR.alternatingSign-suc

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡  (-1ⁿ n) · x
-1ⁿ·≡· = ℚR.alternate≡alternatingSign·

absᵣ∘-1ⁿ· : ∀ n x → abs (-1ⁿ· n x) ≡ abs x
absᵣ∘-1ⁿ· = abs-alternate


^ⁿ-odd : ∀ n x → - (x ^ⁿ suc (n ℕ.· 2)) ≡ ((- x) ^ⁿ suc (n ℕ.· 2))
^ⁿ-even : ∀ n x → (x ^ⁿ (n ℕ.· 2)) ≡ ((- x) ^ⁿ (n ℕ.· 2))

^ⁿ-even = Exponentiationℚ.^-even
^ⁿ-odd = Exponentiationℚ.^-odd


seqSumUpTo : (ℕ → ℚ) → ℕ →  ℚ
seqSumUpTo s zero = 0
seqSumUpTo s (suc n) = s zero + seqSumUpTo (s ∘ suc) n


seqSumUpTo' : (ℕ → ℚ) → ℕ →  ℚ
seqSumUpTo' s zero = 0
seqSumUpTo' s (suc n) = seqSumUpTo' s n + s n

seqΣ : (ℕ → ℚ) → (ℕ → ℚ)
seqΣ = seqSumUpTo'


seqΣ' : (ℕ → ℚ) → (ℕ → ℚ)
seqΣ' = seqSumUpTo
