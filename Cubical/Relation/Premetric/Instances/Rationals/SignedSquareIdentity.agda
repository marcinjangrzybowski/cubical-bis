module Cubical.Relation.Premetric.Instances.Rationals.SignedSquareIdentity where

-- The metric pulled back along x ↦ x |x| is the one-dimensional path
-- metric associated to the (degenerate) metric tensor 4 x² dx².  This
-- module studies the identity chart back to the ordinary rational metric.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open PositiveRationals
open PositiveHalvesℚ

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  signedSquareℚ-nonPositive : ∀ {x : ℚ} → x ≤ 0 →
    signedSquareℚ x ≡ - (x · x)
  signedSquareℚ-nonPositive {x} x≤0 =
    signedSquareℚ≡·abs x
    ∙ cong (x ·_) (≤0→abs≡- x x≤0)
    ∙ ℚRing.-DistR· x x

  signedSquareℚ-nonNegative : ∀ {x : ℚ} → 0 ≤ x →
    signedSquareℚ x ≡ x · x
  signedSquareℚ-nonNegative {x} 0≤x =
    signedSquareℚ≡·abs x ∙ cong (x ·_) (0≤→abs≡id x 0≤x)

  nonnegativeProduct : ∀ {x y : ℚ} → 0 ≤ x → 0 ≤ y → 0 ≤ x · y
  nonnegativeProduct {x} {y} 0≤x 0≤y =
    subst (_≤ x · y) (ℚRing.0LeftAnnihilates y)
      (·MonoR≤ 0 x y 0≤y 0≤x)

  ≤double : ∀ {x : ℚ} → 0 ≤ x → x ≤ 2 · x
  ≤double {x} 0≤x =
    subst2 _≤_ (+IdR x) (x+x≡2x x)
      (ℚ.≤-o+ 0 x x 0≤x)

  positiveSideBound : ∀ {x y : ℚ} → 0 ≤ x → x ≤ y →
    (y - x) · (y - x) ≤ 2 · (y · y - x · x)
  positiveSideBound {x} {y} 0≤x x≤y =
    subst2 _≤_ refl (cong (2 ·_) product≡difference)
      (ℚ.isTrans≤ _ _ _ square≤product
        (≤double (nonnegativeProduct 0≤difference 0≤sum)))
    where
    difference≤sum : y - x ≤ y + x
    difference≤sum = +MonoL≤ (- x) x y
      (ℚ.isTrans≤ (- x) 0 x (0≤→-≤0 x 0≤x) 0≤x)

    0≤difference : 0 ≤ y - x
    0≤difference = ≤→0≤Δ x y x≤y

    0≤sum : 0 ≤ y + x
    0≤sum = ℚ.isTrans≤ _ _ _ 0≤difference difference≤sum

    square≤product :
      (y - x) · (y - x) ≤ (y - x) · (y + x)
    square≤product =
      ·MonoL≤ (y - x) (y + x) (y - x) 0≤difference difference≤sum

    product≡difference : (y - x) · (y + x) ≡ y · y - x · x
    product≡difference = ℚ!

  negativeSideBound : ∀ {x y : ℚ} → x ≤ y → y ≤ 0 →
    (y - x) · (y - x) ≤ 2 · (x · x - y · y)
  negativeSideBound {x} {y} x≤y y≤0 =
    subst2 _≤_ refl (cong (2 ·_) product≡difference)
      (ℚ.isTrans≤ _ _ _ square≤product
        (≤double (nonnegativeProduct 0≤difference 0≤sum)))
    where
    difference≤sum : y - x ≤ - x - y
    difference≤sum = subst2 _≤_ ℚ! ℚ!
      (+MonoL≤ y (- y) (- x)
        (ℚ.isTrans≤ y 0 (- y) y≤0 (≤0→0≤- y y≤0)))

    0≤difference : 0 ≤ y - x
    0≤difference = ≤→0≤Δ x y x≤y

    0≤sum : 0 ≤ - x - y
    0≤sum = ℚ.isTrans≤ _ _ _ 0≤difference difference≤sum

    square≤product :
      (y - x) · (y - x) ≤ (y - x) · (- x - y)
    square≤product =
      ·MonoL≤ (y - x) (- x - y) (y - x) 0≤difference difference≤sum

    product≡difference : (y - x) · (- x - y) ≡ x · x - y · y
    product≡difference = ℚ!

  crossingZeroBound : ∀ x y →
    (y - x) · (y - x) ≤ 2 · (y · y + x · x)
  crossingZeroBound x y = ℚ.≤- _ _
    (subst (0 ≤_) ℚ! (0≤² (x + y)))

  selfDistance : ∀ x → abs (x - x) ≡ 0
  selfDistance x = cong abs (+InvR x)
    ∙ 0≤→abs≡id 0 (ℚ.isRefl≤ 0)

  selfSquareDistanceBound : ∀ x →
    abs (x - x) · abs (x - x)
      ≤ 2 · abs (signedSquareℚ x - signedSquareℚ x)
  selfSquareDistanceBound x =
    subst2 _≤_ (sym leftZero) (sym rightZero) (ℚ.isRefl≤ 0)
    where
    leftZero : abs (x - x) · abs (x - x) ≡ 0
    leftZero = cong₂ _·_ (selfDistance x) (selfDistance x)
      ∙ ℚRing.0LeftAnnihilates 0

    rightZero : 2 · abs (signedSquareℚ x - signedSquareℚ x) ≡ 0
    rightZero = cong (2 ·_) (selfDistance (signedSquareℚ x))
      ∙ ℚRing.0RightAnnihilates 2

  squareDistanceBound< : ∀ {x y : ℚ} → x < y →
    abs (x - y) · abs (x - y)
      ≤ 2 · abs (signedSquareℚ x - signedSquareℚ y)
  squareDistanceBound< {x} {y} x<y =
    subst2 _≤_
      (cong₂ _·_ (sym distance) (sym distance))
      (cong (2 ·_) (sym signedDistance))
      signs
    where
    distance : abs (x - y) ≡ y - x
    distance = <0→abs≡- (x - y) (<→Δ<0 x y x<y) ∙ ℚ!

    signedDistance :
      abs (signedSquareℚ x - signedSquareℚ y)
        ≡ signedSquareℚ y - signedSquareℚ x
    signedDistance =
      <0→abs≡- (signedSquareℚ x - signedSquareℚ y)
        (<→Δ<0 (signedSquareℚ x) (signedSquareℚ y)
          (signedSquareℚ-strictMono x<y))
      ∙ ℚ!

    signs :
      (y - x) · (y - x)
        ≤ 2 · (signedSquareℚ y - signedSquareℚ x)
    signs with x ℚ.≟ 0 | y ℚ.≟ 0
    ... | ℚ.lt x<0 | ℚ.lt y<0 =
      subst2 (λ sx sy → (y - x) · (y - x) ≤ 2 · (sy - sx))
        (sym (signedSquareℚ-nonPositive (<-≤-weaken x 0 x<0)))
        (sym (signedSquareℚ-nonPositive (<-≤-weaken y 0 y<0)))
        (subst ((y - x) · (y - x) ≤_) ℚ!
          (negativeSideBound (<-≤-weaken x y x<y)
            (<-≤-weaken y 0 y<0)))
    ... | ℚ.lt x<0 | ℚ.eq y≡0 =
      subst2 (λ sx sy → (y - x) · (y - x) ≤ 2 · (sy - sx))
        (sym (signedSquareℚ-nonPositive (<-≤-weaken x 0 x<0)))
        (sym (signedSquareℚ-nonPositive (subst (_≤ 0) (sym y≡0) (ℚ.isRefl≤ 0))))
        (subst ((y - x) · (y - x) ≤_) ℚ!
          (negativeSideBound (<-≤-weaken x y x<y)
            (subst (_≤ 0) (sym y≡0) (ℚ.isRefl≤ 0))))
    ... | ℚ.lt x<0 | ℚ.gt 0<y =
      subst2 (λ sx sy → (y - x) · (y - x) ≤ 2 · (sy - sx))
        (sym (signedSquareℚ-nonPositive (<-≤-weaken x 0 x<0)))
        (sym (signedSquareℚ-nonNegative (<-≤-weaken 0 y 0<y)))
        (subst ((y - x) · (y - x) ≤_) ℚ! (crossingZeroBound x y))
    ... | ℚ.eq x≡0 | ℚ.lt y<0 =
      ⊥.rec (ℚ.isIrrefl< 0
        (ℚ.isTrans< 0 y 0 (subst (_< y) x≡0 x<y) y<0))
    ... | ℚ.eq x≡0 | ℚ.eq y≡0 =
      ⊥.rec (ℚ.isIrrefl< 0
        (subst2 _<_ x≡0 y≡0 x<y))
    ... | ℚ.eq x≡0 | ℚ.gt 0<y =
      subst2 (λ sx sy → (y - x) · (y - x) ≤ 2 · (sy - sx))
        (sym (signedSquareℚ-nonNegative
          (subst (0 ≤_) (sym x≡0) (ℚ.isRefl≤ 0))))
        (sym (signedSquareℚ-nonNegative (<-≤-weaken 0 y 0<y)))
        (positiveSideBound
          (subst (0 ≤_) (sym x≡0) (ℚ.isRefl≤ 0))
          (<-≤-weaken x y x<y))
    ... | ℚ.gt 0<x | ℚ.lt y<0 =
      ⊥.rec (ℚ.isIrrefl< 0
        (ℚ.isTrans< 0 y 0 (ℚ.isTrans< 0 x y 0<x x<y) y<0))
    ... | ℚ.gt 0<x | ℚ.eq y≡0 =
      ⊥.rec (ℚ.isIrrefl< 0
        (subst (0 <_) y≡0 (ℚ.isTrans< 0 x y 0<x x<y)))
    ... | ℚ.gt 0<x | ℚ.gt 0<y =
      subst2 (λ sx sy → (y - x) · (y - x) ≤ 2 · (sy - sx))
        (sym (signedSquareℚ-nonNegative (<-≤-weaken 0 x 0<x)))
        (sym (signedSquareℚ-nonNegative (<-≤-weaken 0 y 0<y)))
        (positiveSideBound (<-≤-weaken 0 x 0<x) (<-≤-weaken x y x<y))

-- This is the global comparison between the tensor metric and the ordinary
-- metric.  The factor 2 is only needed when the interval crosses zero.
squareDistanceBound : ∀ x y →
  abs (x - y) · abs (x - y)
    ≤ 2 · abs (signedSquareℚ x - signedSquareℚ y)
squareDistanceBound x y with x ℚ.≟ y
... | ℚ.lt x<y = squareDistanceBound< x<y
... | ℚ.eq x≡y = subst (λ y →
    abs (x - y) · abs (x - y)
      ≤ 2 · abs (signedSquareℚ x - signedSquareℚ y))
    x≡y (selfSquareDistanceBound x)
... | ℚ.gt y<x =
  subst2 _≤_
    (sym (cong₂ _·_ (abs-Comm x y) (abs-Comm x y)))
    (sym (cong (2 ·_) (abs-Comm (signedSquareℚ x) (signedSquareℚ y))))
    (squareDistanceBound< y<x)

signedToOrdinaryModulus : ℚ₊ → ℚ₊
signedToOrdinaryModulus ε = (ε ·₊ ε) /2₊

private
  twoPositive : 0 < 2
  twoPositive = ℚ.0<sucN 1

  squareReflects< : ∀ {x y : ℚ} → 0 ≤ x → 0 < y →
    x · x < y · y → x < y
  squareReflects< {x} {y} 0≤x 0<y x²<y² with x ℚ.≟ y
  ... | ℚ.lt x<y = x<y
  ... | ℚ.eq x≡y = ⊥.rec (ℚ.isIrrefl< (y · y)
    (subst (_< y · y) (cong₂ _·_ x≡y x≡y) x²<y²))
  ... | ℚ.gt y<x = ⊥.rec (ℚ.isAsym< (x · x) (y · y)
    x²<y² (ℚ.isTrans≤< (y · y) (x · y) (x · x)
      (·MonoR≤ y x y (<-≤-weaken 0 y 0<y)
        (<-≤-weaken y x y<x))
      (·MonoL< y x x (ℚ.isTrans< _ _ _ 0<y y<x) y<x)))

identitySignedToOrdinary-ucWith :
  IsUniformlyContinuousWith
    (snd ℚSignedSquarePremetricSpace)
    (idfun ℚ)
    (snd ℚPremetricSpace)
    signedToOrdinaryModulus
IsUniformlyContinuousWith.pres≈ identitySignedToOrdinary-ucWith x y ε sqClose =
  squareReflects< (0≤abs (x - y)) (snd ε)
    (ℚ.isTrans≤< _ _ _ (squareDistanceBound x y)
      (subst (2 · abs (signedSquareℚ x - signedSquareℚ y) <_)
        ℚ!
        (ℚ.<-o·
          (abs (signedSquareℚ x - signedSquareℚ y))
          (fst (signedToOrdinaryModulus ε)) 2
          twoPositive sqClose)))

-- The identity chart is uniformly continuous in this direction, with a
-- square-root modulus.  It is not globally Lipschitz.
identitySignedToOrdinaryᵘᶜ :
  UC[ ℚSignedSquarePremetricSpace , ℚPremetricSpace ]
fst identitySignedToOrdinaryᵘᶜ = idfun ℚ
snd identitySignedToOrdinaryᵘᶜ =
  ∣ signedToOrdinaryModulus , identitySignedToOrdinary-ucWith ∣₁
