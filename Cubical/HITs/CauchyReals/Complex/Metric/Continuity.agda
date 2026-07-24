module Cubical.HITs.CauchyReals.Complex.Metric.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Mappings
open import Cubical.HITs.CauchyReals.Complex.Metric.Operations

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


IsComplexContinuousAt : (ℂ → ℂ) → ℂ → Type₀
IsComplexContinuousAt f =
  IsContinuousAt
    (snd ℂPremetricSpace) f
    (snd ℂPremetricSpace)


IsComplexContinuous : (ℂ → ℂ) → Type₀
IsComplexContinuous f =
  isContinuous
    (snd ℂPremetricSpace) f
    (snd ℂPremetricSpace)


IsComplexLipschitzWith :
  ℚ₊ → (ℂ → ℂ) → Type₀
IsComplexLipschitzWith L f =
  IsLipschitzWith
    (snd ℂPremetricSpace) f
    (snd ℂPremetricSpace) L


translateRightℂContinuous :
  ∀ u →
  IsComplexContinuous (_+ℂ u)
translateRightℂContinuous u =
  isNonExpanding→isContinuous
    (snd ℂPremetricSpace) (_+ℂ u)
    (snd ℂPremetricSpace)
    (translateℂIsNonExpanding u)


translateRightℂC :
  ℂ → C[ ℂPremetricSpace , ℂPremetricSpace ]
translateRightℂC u =
  (_+ℂ u) , translateRightℂContinuous u


translateLeftℂIsNonExpanding :
  ∀ u →
  IsNonExpanding
    (snd ℂPremetricSpace) (u +ℂ_)
    (snd ℂPremetricSpace)
translateLeftℂIsNonExpanding u
  .IsNonExpanding.pres≈ =
  translateLeftℂ-pres≈ u


translateLeftℂContinuous :
  ∀ u →
  IsComplexContinuous (u +ℂ_)
translateLeftℂContinuous u =
  isNonExpanding→isContinuous
    (snd ℂPremetricSpace) (u +ℂ_)
    (snd ℂPremetricSpace)
    (translateLeftℂIsNonExpanding u)


translateLeftℂC :
  ℂ → C[ ℂPremetricSpace , ℂPremetricSpace ]
translateLeftℂC u =
  (u +ℂ_) , translateLeftℂContinuous u


leftMultiplyℂ : ℂ → ℂ → ℂ
leftMultiplyℂ c z =
  c ·ℂ z


opaque
  leftMultiplyDifference : ∀ c z w →
    leftMultiplyℂ c z -ℂ leftMultiplyℂ c w ≡
    c ·ℂ (z -ℂ w)
  leftMultiplyDifference c z w =
    ℂ≡ ℝ! ℝ!


opaque
  leftMultiplyℂ-pres≈ :
    ∀ c (bound : ComplexScalarBound c) z w ε →
    z ≈ℂ[ ε ] w →
    leftMultiplyℂ c z
      ≈ℂ[ fst bound ·₊ ε ]
    leftMultiplyℂ c w
  leftMultiplyℂ-pres≈
    c (M , |c|≤M) z w ε z≈w =
    subst
      (_<ᵣ rat (fst (M ·₊ ε)))
      (sym
        (cong modulus
          (leftMultiplyDifference c z w)
        ∙ modulus-mul c (z -ℂ w)))
      (boundedModulusProductAtRadius<
        c (z -ℂ w) M ε
        |c|≤M z≈w)


leftMultiplyℂIsLipschitzWith :
  ∀ c (bound : ComplexScalarBound c) →
  IsComplexLipschitzWith (fst bound)
    (leftMultiplyℂ c)
leftMultiplyℂIsLipschitzWith c bound
  .IsLipschitzWith.pres≈ =
  leftMultiplyℂ-pres≈ c bound


leftMultiplyℂLipschitzFromBound :
  ∀ c →
  ComplexScalarBound c →
  isLipschitz
    (snd ℂPremetricSpace) (leftMultiplyℂ c)
    (snd ℂPremetricSpace)
leftMultiplyℂLipschitzFromBound c bound =
  ∣ fst bound ,
    leftMultiplyℂIsLipschitzWith c bound ∣₁


leftMultiplyℂLipschitz :
  ∀ c →
  isLipschitz
    (snd ℂPremetricSpace) (leftMultiplyℂ c)
    (snd ℂPremetricSpace)
leftMultiplyℂLipschitz c =
  PT.map
    (λ bound →
      fst bound ,
      leftMultiplyℂIsLipschitzWith c bound)
    (complexScalarHasRationalBound c)


leftMultiplyℂContinuousFromBound :
  ∀ c →
  ComplexScalarBound c →
  IsComplexContinuous (leftMultiplyℂ c)
leftMultiplyℂContinuousFromBound c bound =
  isLipschitz→isContinuous
    (snd ℂPremetricSpace) (leftMultiplyℂ c)
    (snd ℂPremetricSpace)
    (leftMultiplyℂLipschitzFromBound c bound)


leftMultiplyℂContinuous :
  ∀ c →
  IsComplexContinuous (leftMultiplyℂ c)
leftMultiplyℂContinuous c =
  isLipschitz→isContinuous
    (snd ℂPremetricSpace) (leftMultiplyℂ c)
    (snd ℂPremetricSpace)
    (leftMultiplyℂLipschitz c)


leftMultiplyℂL :
  ℂ → L[ ℂPremetricSpace , ℂPremetricSpace ]
leftMultiplyℂL c =
  leftMultiplyℂ c , leftMultiplyℂLipschitz c


leftMultiplyℂC :
  ℂ →
  C[ ℂPremetricSpace , ℂPremetricSpace ]
leftMultiplyℂC c =
  leftMultiplyℂ c ,
  leftMultiplyℂContinuous c


rightMultiplyℂ : ℂ → ℂ → ℂ
rightMultiplyℂ c z =
  z ·ℂ c


opaque
  rightMultiplyDifference : ∀ c z w →
    rightMultiplyℂ c z -ℂ rightMultiplyℂ c w ≡
    c ·ℂ (z -ℂ w)
  rightMultiplyDifference c z w =
    ℂ≡ ℝ! ℝ!


opaque
  rightMultiplyℂ-pres≈ :
    ∀ c (bound : ComplexScalarBound c) z w ε →
    z ≈ℂ[ ε ] w →
    rightMultiplyℂ c z
      ≈ℂ[ fst bound ·₊ ε ]
    rightMultiplyℂ c w
  rightMultiplyℂ-pres≈
    c (M , |c|≤M) z w ε z≈w =
    subst
      (_<ᵣ rat (fst (M ·₊ ε)))
      (sym
        (cong modulus
          (rightMultiplyDifference c z w)
        ∙ modulus-mul c (z -ℂ w)))
      (boundedModulusProductAtRadius<
        c (z -ℂ w) M ε
        |c|≤M z≈w)


rightMultiplyℂIsLipschitzWith :
  ∀ c (bound : ComplexScalarBound c) →
  IsComplexLipschitzWith (fst bound)
    (rightMultiplyℂ c)
rightMultiplyℂIsLipschitzWith c bound
  .IsLipschitzWith.pres≈ =
  rightMultiplyℂ-pres≈ c bound


rightMultiplyℂLipschitzFromBound :
  ∀ c →
  ComplexScalarBound c →
  isLipschitz
    (snd ℂPremetricSpace) (rightMultiplyℂ c)
    (snd ℂPremetricSpace)
rightMultiplyℂLipschitzFromBound c bound =
  ∣ fst bound ,
    rightMultiplyℂIsLipschitzWith c bound ∣₁


rightMultiplyℂLipschitz :
  ∀ c →
  isLipschitz
    (snd ℂPremetricSpace) (rightMultiplyℂ c)
    (snd ℂPremetricSpace)
rightMultiplyℂLipschitz c =
  PT.map
    (λ bound →
      fst bound ,
      rightMultiplyℂIsLipschitzWith c bound)
    (complexScalarHasRationalBound c)


rightMultiplyℂContinuousFromBound :
  ∀ c →
  ComplexScalarBound c →
  IsComplexContinuous (rightMultiplyℂ c)
rightMultiplyℂContinuousFromBound c bound =
  isLipschitz→isContinuous
    (snd ℂPremetricSpace) (rightMultiplyℂ c)
    (snd ℂPremetricSpace)
    (rightMultiplyℂLipschitzFromBound c bound)


rightMultiplyℂContinuous :
  ∀ c →
  IsComplexContinuous (rightMultiplyℂ c)
rightMultiplyℂContinuous c =
  isLipschitz→isContinuous
    (snd ℂPremetricSpace) (rightMultiplyℂ c)
    (snd ℂPremetricSpace)
    (rightMultiplyℂLipschitz c)


rightMultiplyℂL :
  ℂ → L[ ℂPremetricSpace , ℂPremetricSpace ]
rightMultiplyℂL c =
  rightMultiplyℂ c , rightMultiplyℂLipschitz c


rightMultiplyℂC :
  ℂ →
  C[ ℂPremetricSpace , ℂPremetricSpace ]
rightMultiplyℂC c =
  rightMultiplyℂ c ,
  rightMultiplyℂContinuous c
