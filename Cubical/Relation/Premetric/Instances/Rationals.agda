module Cubical.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue using (sign; abs≡sign·)
open import Cubical.Data.Sum using (inl; inr)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Subspace

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals

open PremetricStr

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

ℚPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℚPremetricSpace = ℚ
_≈[_]_ (snd ℚPremetricSpace) = λ x ε y → abs (x - y) < ⟨ ε ⟩₊
isPremetric (snd ℚPremetricSpace) = isPMℚ where
  open IsPremetric

  isPMℚ : IsPremetric _
  isPMℚ .isSetM = isSetℚ
  isPMℚ .isProp≈ x y ε = is-prop-valued< (abs (x - y)) ⟨ ε ⟩₊
  isPMℚ .isRefl≈ x ε = ℚ.recompute< $ subst ((_< ⟨ ε ⟩₊) ∘ abs) (sym (+InvR x)) (ε .snd)
  isPMℚ .isSym≈ x y ε = ℚ.recompute< ∘ (subst (_< ⟨ ε ⟩₊) $ abs-Comm x y)
  isPMℚ .isSeparated≈ = selfSeparated
  isPMℚ .isTriangular≈ x y z ε δ <ε <δ = ℚ.recompute< $ begin<
    abs (x - z)                 ≤⟨ triangularInequality- x z y ⟩
    abs (x - y) + abs (y - z)   <⟨ +Mono< (abs (x - y)) ⟨ ε ⟩₊ _ _ <ε <δ ⟩
    ⟨ ε +₊ δ ⟩₊                  ◾
  isPMℚ .isRounded≈ x y ε <ε =
    ∣ (mean (abs(x - y)) ⟨ ε ⟩₊ , ℚ.isTrans≤< _ _ _ (0≤abs (x - y)) (<→<mean _ ⟨ ε ⟩₊ <ε))
    , ℚ.recompute< (<→mean< (abs(x - y)) ⟨ ε ⟩₊ <ε)
    , ℚ.recompute< (<→<mean (abs(x - y)) ⟨ ε ⟩₊ <ε) ∣₁


signedSquareℚ : ℚ → ℚ
signedSquareℚ x = sign x · x · x

signedSquareℚ≡·abs : ∀ x → signedSquareℚ x ≡ x · abs x
signedSquareℚ≡·abs x =
  sym (·Assoc (sign x) x x)
  ∙ ·Comm (sign x) (x · x)
  ∙ sym (·Assoc x x (sign x))
  ∙ cong (x ·_) (sym (abs≡sign· x))

private
  square-strictMono : ∀ {x y : ℚ} → 0 ≤ x → x < y → x · x < y · y
  square-strictMono {x} {y} 0≤x x<y = begin<
    x · x ≤⟨ ·MonoR≤ x y x 0≤x (<-≤-weaken x y x<y) ⟩
    y · x <⟨ ·MonoL< x y y (≤-<-trans 0 x y 0≤x x<y) x<y ⟩
    y · y ◾

  signedSquareℚ<0 : ∀ {x : ℚ} → x < 0 → signedSquareℚ x < 0
  signedSquareℚ<0 {x} x<0 = begin<
    signedSquareℚ x ≡→≤⟨ signedSquareℚ≡·abs x ∙ cong (x ·_) (<0→abs≡- x x<0) ∙ ℚRing.-DistR· x x ⟩
    - (x · x)       <⟨ 0<→-<0 (x · x) (#→0<² x (inl x<0)) ⟩
    0                   ◾

  0<signedSquareℚ : ∀ {x : ℚ} → 0 < x → 0 < signedSquareℚ x
  0<signedSquareℚ {x} 0<x = begin<
    0                   <⟨ #→0<² x (inr 0<x) ⟩
    x · x             ≡→≤⟨ sym (cong (x ·_) (0<→abs≡id x 0<x)) ∙ sym (signedSquareℚ≡·abs x) ⟩
    signedSquareℚ x ◾

  signedSquareℚ0 : signedSquareℚ 0 ≡ 0
  signedSquareℚ0 = signedSquareℚ≡·abs 0 ∙ ℚRing.0LeftAnnihilates (abs 0)

signedSquareℚ-strictMono : ∀ {x y : ℚ} → x < y → signedSquareℚ x < signedSquareℚ y
signedSquareℚ-strictMono {x} {y} x<y with x ℚ.≟ 0 | y ℚ.≟ 0
... | ℚ.lt x<0 | ℚ.lt y<0 = begin<
  signedSquareℚ x ≡→≤⟨ signedSquareℚ≡·abs x ∙ cong (x ·_) (<0→abs≡- x x<0) ∙ ℚRing.-DistR· x x ⟩
  - (x · x)       <⟨ -Flip< (y · y) (x · x) (begin<
    y · y             ≡→≤⟨ sym (ℚRing.-Dist· y y) ⟩
    (- y) · (- y)   <⟨ square-strictMono (<-≤-weaken 0 (- y) (<0→0<- y y<0)) (-Flip< x y x<y) ⟩
    (- x) · (- x)   ≡→≤⟨ ℚRing.-Dist· x x ⟩
    x · x             ◾) ⟩
  - (y · y)       ≡→≤⟨ sym (signedSquareℚ≡·abs y ∙ cong (y ·_) (<0→abs≡- y y<0) ∙ ℚRing.-DistR· y y) ⟩
  signedSquareℚ y ◾
... | ℚ.lt x<0 | ℚ.eq y≡0 = begin<
  signedSquareℚ x <⟨ signedSquareℚ<0 x<0 ⟩
  0                   ≡→≤⟨ sym (cong signedSquareℚ y≡0 ∙ signedSquareℚ0) ⟩
  signedSquareℚ y ◾
... | ℚ.lt x<0 | ℚ.gt 0<y = begin<
  signedSquareℚ x <⟨ signedSquareℚ<0 x<0 ⟩
  0                   <⟨ 0<signedSquareℚ 0<y ⟩
  signedSquareℚ y ◾
... | ℚ.eq x≡0 | ℚ.lt y<0 = ⊥.rec (ℚ.isIrrefl< 0 (begin<
  0 ≡→≤⟨ sym x≡0 ⟩ x <⟨ x<y ⟩ y <⟨ y<0 ⟩ 0 ◾))
... | ℚ.eq x≡0 | ℚ.eq y≡0 = ⊥.rec (ℚ.isIrrefl< 0 (begin<
  0 ≡→≤⟨ sym x≡0 ⟩ x <⟨ x<y ⟩ y ≡→≤⟨ y≡0 ⟩ 0 ◾))
... | ℚ.eq x≡0 | ℚ.gt 0<y = begin<
  signedSquareℚ x ≡→≤⟨ cong signedSquareℚ x≡0 ∙ signedSquareℚ0 ⟩
  0                   <⟨ 0<signedSquareℚ 0<y ⟩
  signedSquareℚ y ◾
... | ℚ.gt 0<x | ℚ.lt y<0 = ⊥.rec (ℚ.isIrrefl< 0 (begin<
  0 <⟨ 0<x ⟩ x <⟨ x<y ⟩ y <⟨ y<0 ⟩ 0 ◾))
... | ℚ.gt 0<x | ℚ.eq y≡0 = ⊥.rec (ℚ.isIrrefl< 0 (begin<
  0 <⟨ 0<x ⟩ x <⟨ x<y ⟩ y ≡→≤⟨ y≡0 ⟩ 0 ◾))
... | ℚ.gt 0<x | ℚ.gt 0<y = begin<
  signedSquareℚ x ≡→≤⟨ signedSquareℚ≡·abs x ∙ cong (x ·_) (0<→abs≡id x 0<x) ⟩
  x · x             <⟨ square-strictMono (<-≤-weaken 0 x 0<x) x<y ⟩
  y · y             ≡→≤⟨ sym (cong (y ·_) (0<→abs≡id y 0<y)) ∙ sym (signedSquareℚ≡·abs y) ⟩
  signedSquareℚ y ◾

signedSquareℚ-injective : ∀ x y → signedSquareℚ x ≡ signedSquareℚ y → x ≡ y
signedSquareℚ-injective x y sqx≡sqy with x ℚ.≟ y
... | ℚ.lt x<y = ⊥.rec (ℚ.isIrrefl< (signedSquareℚ y)
  (subst (_< signedSquareℚ y) sqx≡sqy (signedSquareℚ-strictMono x<y)))
... | ℚ.eq x≡y = x≡y
... | ℚ.gt y<x = ⊥.rec (ℚ.isIrrefl< (signedSquareℚ x)
  (subst (_< signedSquareℚ x) (sym sqx≡sqy) (signedSquareℚ-strictMono y<x)))

private
  module SignedSquarePremetric = SubspaceAlongInjection
    ℚPremetricSpace isSetℚ signedSquareℚ signedSquareℚ-injective

ℚSignedSquarePremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℚSignedSquarePremetricSpace = SignedSquarePremetric.injectionPremetricSpace
