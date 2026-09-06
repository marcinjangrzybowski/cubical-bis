module Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
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
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Factors
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform

open PositiveRationals using (ℚ₊)

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


uniformlyContinuousDifferenceFactorGivesUniformDerivative :
  ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) (factor : A × A → ℝ) →
  (∀ x y → function y - function x ≡
    (coordinate y - coordinate x) · factor (x , y)) →
  (∀ x → factor (x , x) ≡ derivative x) →
  IsRadiuswiseUniformlyContinuous (PremetricProductStr source source)
    factor (ℝPremetricSpace .snd) →
  IsRadiuswiseUniformDerivativeAlong source coordinate function derivative
uniformlyContinuousDifferenceFactorGivesUniformDerivative
    source coordinate function derivative factor factorization diagonal factor-uc ε =
  PT.map (λ { (δ , preserves) → δ , λ x y near →
    error-bound x y
      (preserves (x , x) (x , y)
        (PremetricStr.isRefl≈ source x δ , near)) }) (factor-uc ε)
  where
  error-path : ∀ x y → derivativeErrorAlong coordinate function derivative x y ≡
    (coordinate y - coordinate x) · (factor (x , y) - factor (x , x))
  error-path x y =
    cong (_- (derivative x · (coordinate y - coordinate x))) (factorization x y)
    ∙ cong (((coordinate y - coordinate x) · factor (x , y)) -_)
        (mulComm (derivative x) (coordinate y - coordinate x))
    ∙ sym (ℝRing.·DistR- (coordinate y - coordinate x) (factor (x , y)) (derivative x))
    ∙ cong (λ value → (coordinate y - coordinate x) · (factor (x , y) - value))
        (sym (diagonal x))

  factor-bound : ∀ x y → factor (x , x) ∼[ ε ] factor (x , y) →
    absℝ (factor (x , y) - factor (x , x)) ≤ℝ rat (fst ε)
  factor-bound x y close =
    subst (_≤ℝ rat (fst ε)) (distanceSym (factor (x , x)) (factor (x , y)))
      (<ℝ-weaken (absℝ (factor (x , x) - factor (x , y))) (rat (fst ε))
        (closeness→absDifference< (factor (x , x)) (factor (x , y)) ε close))

  error-bound : ∀ x y → factor (x , x) ∼[ ε ] factor (x , y) →
    absℝ (derivativeErrorAlong coordinate function derivative x y) ≤ℝ
    rat (fst ε) · absℝ (coordinate y - coordinate x)
  error-bound x y close =
    subst (_≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))
      (sym
        (cong absℝ (error-path x y)
        ∙ absMul (coordinate y - coordinate x) (factor (x , y) - factor (x , x))
        ∙ mulComm (absℝ (coordinate y - coordinate x))
            (absℝ (factor (x , y) - factor (x , x)))))
      (mulPres≤R-0≤ (absℝ (factor (x , y) - factor (x , x))) (rat (fst ε))
        (absℝ (coordinate y - coordinate x))
        (absNonnegative (coordinate y - coordinate x)) (factor-bound x y close))


powerSeriesUniformValueHasUniformFormalDerivativeOnClosedRadius :
  ∀ coefficients radius → 0ℝ ≤ℝ radius →
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (derivative-uniform : FormalDerivativePowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (factor-uniform : PowerSeriesDifferenceFactorUniformlyCauchyOnRadius coefficients radius) →
  IsRadiuswiseUniformDerivativeAlong (ClosedAbsRadiusPremetricSpace radius .snd) fst
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius coefficients radius derivative-uniform)
powerSeriesUniformValueHasUniformFormalDerivativeOnClosedRadius
    coefficients radius 0≤radius uniform derivative-uniform factor-uniform =
  uniformlyContinuousDifferenceFactorGivesUniformDerivative
    (ClosedAbsRadiusPremetricSpace radius .snd) fst
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius coefficients radius derivative-uniform)
    (powerSeriesDifferenceFactorValueOnClosedRadius coefficients radius factor-uniform)
    (λ x y → powerSeriesValueDifferenceFactorization coefficients (fst x) (fst y)
      (uniformlyCauchySeriesSummableAt uniform x)
      (uniformlyCauchySeriesSummableAt uniform y)
      (uniformlyCauchySeriesSummableAt factor-uniform (x , y)))
    (λ x → powerSeriesDifferenceFactorDiagonalValue coefficients (fst x)
      (uniformlyCauchySeriesSummableAt factor-uniform (x , x))
      (uniformlyCauchySeriesSummableAt derivative-uniform x))
    (powerSeriesDifferenceFactorValueIsRadiuswiseUniformlyContinuous
      radius 0≤radius coefficients factor-uniform)
