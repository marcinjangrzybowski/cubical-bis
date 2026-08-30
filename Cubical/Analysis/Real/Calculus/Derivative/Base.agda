module Cubical.Analysis.Real.Calculus.Derivative.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Metric.Distance

open PositiveRationals

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- The division-free first-order remainder.  The derivative is evaluated at
-- the base point, so this also makes sense for maps on a premetric subspace.

derivativeErrorAlong :
  ∀ {ℓ} {A : Type ℓ} →
  (coordinate function derivative : A → ℝ) →
  A → A → ℝ
derivativeErrorAlong coordinate function derivative x y =
  (function y - function x) -
    derivative x · (coordinate y - coordinate x)


IsDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A →
  (coordinate function derivative : A → ℝ) →
  Type (ℓ-max ℓ ℓ')
IsDerivativeAlong source coordinate function derivative =
  ∀ x (ε : ℚ₊) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      PremetricStr._≈[_]_ source x δ y →
      absℝ
          (derivativeErrorAlong
            coordinate function derivative x y)
        ≤ℝ
      rat (fst ε) · absℝ (coordinate y - coordinate x))


IsDerivative : (function derivative : ℝ → ℝ) → Type
IsDerivative =
  IsDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)


IsDerivativeAt :
  (function : ℝ → ℝ) → ℝ → ℝ → Type
IsDerivativeAt function derivative-value x =
  ∀ (ε : ℚ₊) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      x ∼[ δ ] y →
      absℝ
          ((function y - function x) -
            derivative-value · (y - x))
        ≤ℝ
      rat (fst ε) · absℝ (y - x))


isDerivativeAt :
  ∀ function derivative →
  IsDerivative function derivative →
  ∀ x → IsDerivativeAt function (derivative x) x
isDerivativeAt function derivative has-derivative x =
  has-derivative x


-- Only the target neighbourhood is pulled back.  No modulus for the map or
-- derivative is selected globally.

pullbackHasDerivativeAlong :
  ∀ {ℓA ℓA' ℓB ℓB'}
    {A : Type ℓA} {B : Type ℓB}
    (source : PremetricStr ℓA' A)
    (target : PremetricStr ℓB' B)
    (coordinate function derivative : B → ℝ)
    (map : A → B) →
  isContinuous source map target →
  IsDerivativeAlong target coordinate function derivative →
  IsDerivativeAlong
    source
    (coordinate ∘ map)
    (function ∘ map)
    (derivative ∘ map)
pullbackHasDerivativeAlong
  source target coordinate function derivative map
  map-continuous has-derivative x ε = do
    (δ , derivative-bound) ← has-derivative (map x) ε
    (η , map-near) ←
      map-continuous x .IsContinuousAt.pres≈ δ
    return
      ( η
      , λ y x≈y →
          derivative-bound (map y) (map-near y x≈y)
      )


private
  differenceFactorErrorPath :
    ∀ difference derivative-value factor-value →
    (difference · factor-value) -
        (derivative-value · difference)
      ≡
    difference · (factor-value - derivative-value)
  differenceFactorErrorPath
    difference derivative-value factor-value =
    cong
      (λ value →
        (difference · factor-value) - value)
      (mulComm derivative-value difference)
    ∙ sym
      (ℝRing.·DistR-
        difference factor-value derivative-value)


-- A continuous divided difference gives a derivative.  The factor need not
-- be defined by division; polynomial and affine factors can be supplied by
-- exact algebraic identities.

continuousDifferenceFactorGivesDerivative :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ)
    (factor : A × A → ℝ) →
  (∀ x y →
    function y - function x ≡
    (coordinate y - coordinate x) · factor (x , y)) →
  (∀ x → factor (x , x) ≡ derivative x) →
  isContinuous
    (PremetricProductStr source source)
    factor
    (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate function derivative
continuousDifferenceFactorGivesDerivative
  source coordinate function derivative factor
  factorization diagonal factor-continuous
  x ε = do
    (δ , factor-preserves) ←
      factor-continuous (x , x) .IsContinuousAt.pres≈ ε
    return
      ( δ
      , λ y x≈y →
          factor-error-bound y
            (factor-preserves
              (x , y)
              ( PremetricStr.isRefl≈ source x δ
              , x≈y
              ))
      )
  where
  factor-error-path : ∀ y →
    derivativeErrorAlong coordinate function derivative x y ≡
    (coordinate y - coordinate x) ·
      (factor (x , y) - factor (x , x))
  factor-error-path y =
    cong
      (_- (derivative x · (coordinate y - coordinate x)))
      (factorization x y)
    ∙ differenceFactorErrorPath
      (coordinate y - coordinate x)
      (derivative x)
      (factor (x , y))
    ∙ cong
      ((coordinate y - coordinate x) ·_)
      (cong (λ value → factor (x , y) - value)
        (sym (diagonal x)))

  factor-difference-bound : ∀ y →
    factor (x , x) ∼[ ε ] factor (x , y) →
    absℝ (factor (x , y) - factor (x , x))
      ≤ℝ rat (fst ε)
  factor-difference-bound y close =
    subst
      (_≤ℝ rat (fst ε))
      (distanceSym (factor (x , x)) (factor (x , y)))
      (<ℝ-weaken
        (absℝ (factor (x , x) - factor (x , y)))
        (rat (fst ε))
        (closeness→absDifference<
          (factor (x , x)) (factor (x , y)) ε close))

  factor-error-bound : ∀ y →
    factor (x , x) ∼[ ε ] factor (x , y) →
    absℝ
        (derivativeErrorAlong coordinate function derivative x y)
      ≤ℝ
    rat (fst ε) · absℝ (coordinate y - coordinate x)
  factor-error-bound y close =
    subst2 _≤ℝ_
      (sym
        ( cong absℝ (factor-error-path y)
        ∙ absMul
            (coordinate y - coordinate x)
            (factor (x , y) - factor (x , x))
        ∙ mulComm
            (absℝ (coordinate y - coordinate x))
            (absℝ (factor (x , y) - factor (x , x)))))
      refl
      (mulPres≤R-0≤
        (absℝ (factor (x , y) - factor (x , x)))
        (rat (fst ε))
        (absℝ (coordinate y - coordinate x))
        (absNonnegative (coordinate y - coordinate x))
        (factor-difference-bound y close))
