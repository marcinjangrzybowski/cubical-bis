module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Sequence
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.NativeBounds as Real
import Cubical.Analysis.Real.Series.Uniform as Real
import Cubical.Analysis.Real.Series.PointwiseLimit as Real
import Cubical.Analysis.Real.Series.PowerSeries.WeightedBound as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Approximation

open PositiveRationals using (ℚ₊)

-- A single majorant, with its native Cauchy witness, controls every finite
-- translated polynomial. Both the radius gap and rational size bound are
-- selected only inside this one propositional truncation.
FiniteTranslationNativeMajorant : ComplexSequence → ℂ → ℝ → Type₀
FiniteTranslationNativeMajorant coefficients center radius =
  Σ[ majorant ∈ Real.RealSequence ]
    Real.IsCauchySeries majorant ×
    (∀ count order → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order
      ≤ℝ majorant order)

opaque
  mereFiniteTranslationNativeMajorant : ∀ coefficients outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    ∀ center radius → 0ℝ ≤ℝ radius → normℂ center + radius <ℝ outer →
    ∥ FiniteTranslationNativeMajorant coefficients center radius ∥₁
  mereFiniteTranslationNativeMajorant coefficients outer witness center radius nonnegative strict =
    PT.rec squash₁ withGap strict
    where
    withGap : PositiveGap (normℂ center + radius) outer →
      ∥ FiniteTranslationNativeMajorant coefficients center radius ∥₁
    withGap (gap , fitsGap) = PT.map withBound
      (Real.mereCauchySeriesUniformPartialSumAbsBound (complexPowerSeriesMajorant coefficients outer) witness)
      where
      larger : ℝ
      larger = radius + rat (fst gap)

      strictLarger : radius <ℝ larger
      strictLarger = subst (_<ℝ larger) (addIdR radius)
        (<ℝ-addL 0ℝ (rat (fst gap)) radius (<ℚ→<ℝ 0 (fst gap) (snd gap)))

      largerNonnegative : 0ℝ ≤ℝ larger
      largerNonnegative = ≤ℝ-trans 0ℝ radius larger nonnegative (<ℝ-weaken radius larger strictLarger)

      fits : normℂ center + larger ≤ℝ outer
      fits = subst (_≤ℝ outer) (sym (addAssoc (normℂ center) radius (rat (fst gap)))) fitsGap

      withBound : (Σ[ bound ∈ ℚ₊ ] (∀ count →
          absℝ (Real.partialSum (complexPowerSeriesMajorant coefficients outer) count) ≤ℝ rat (fst bound))) →
        FiniteTranslationNativeMajorant coefficients center radius
      withBound (bound , bounded) =
        Real.weightedBoundMajorant radius larger nonnegative strictLarger bound ,
        Real.weightedBoundMajorantIsCauchy radius larger nonnegative strictLarger bound ,
        λ count order → Real.weightedCoefficientTermBound radius larger nonnegative strictLarger
          (normℂ (finiteTranslatedCoefficientsℂ coefficients center count order)) bound order
          (finiteTranslatedCoefficientBound coefficients center larger outer (rat (fst bound)) largerNonnegative fits
            (λ n → ≤ℝ-trans (Real.partialSum (complexPowerSeriesMajorant coefficients outer) n)
              (absℝ (Real.partialSum (complexPowerSeriesMajorant coefficients outer) n)) (rat (fst bound))
              (leAbs (Real.partialSum (complexPowerSeriesMajorant coefficients outer) n)) (bounded n)) count order)

  finiteTranslatedMajorantsUniformlyCauchy : ∀ coefficients outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    ∀ center radius → 0ℝ ≤ℝ radius → normℂ center + radius <ℝ outer →
    Real.UniformlyCauchySeries ℕ (λ count → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
  finiteTranslatedMajorantsUniformlyCauchy coefficients outer witness center radius nonnegative strict =
    PT.rec squash₁ fromMajorant (mereFiniteTranslationNativeMajorant coefficients outer witness center radius nonnegative strict)
    where
    fromMajorant : FiniteTranslationNativeMajorant coefficients center radius →
      Real.UniformlyCauchySeries ℕ (λ count → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
    fromMajorant (majorant , native , bounded) = Real.uniformlyDominatedSeriesIsUniformlyCauchy
      (λ count → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
      majorant (λ count order → subst (_≤ℝ majorant order) (sym (absOfNonnegative
        (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order)
        (isNonnegative→0≤ (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order)
          (mulPresIsNonnegative (normℂ (finiteTranslatedCoefficientsℂ coefficients center count order)) (powℝ radius order)
            (0≤→isNonnegative (normℂ (finiteTranslatedCoefficientsℂ coefficients center count order))
              (normℂ-nonnegative (finiteTranslatedCoefficientsℂ coefficients center count order)))
            (powPresIsNonnegative radius order (0≤→isNonnegative radius nonnegative)))))) (bounded count order)) native

  finiteTranslatedPowerSeriesUniformlyCauchy : ∀ coefficients outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    ∀ center radius → 0ℝ ≤ℝ radius → normℂ center + radius <ℝ outer →
    ∀ increment → normℂ increment ≤ℝ radius →
    UniformlyComplexCauchySeries ℕ (λ count → powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment)
  finiteTranslatedPowerSeriesUniformlyCauchy coefficients outer witness center radius nonnegative strict increment boundedIncrement =
    PT.rec (isPropUniformlyComplexCauchySeries ℕ
      (λ count → powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment))
      (λ { (majorant , native , bounded) → uniformlyDominatedComplexSeriesIsUniformlyCauchy
        (λ count → powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment) majorant
        (λ count order → ≤ℝ-trans
          (normℂ (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment order))
          (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order) (majorant order)
          (complexPowerSeriesTermBound (finiteTranslatedCoefficientsℂ coefficients center count) increment radius boundedIncrement order)
          (bounded count order)) native })
      (mereFiniteTranslationNativeMajorant coefficients outer witness center radius nonnegative strict)

  -- The full translated Taylor series now has native convergence data.
  -- Coefficientwise limits transfer the common modulus proved above.
  translatedTaylorMajorantIsCauchy : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
    (center : ℂ) (inside : normℂ center <ℝ outer) radius →
    0ℝ ≤ℝ radius → normℂ center + radius <ℝ outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant
      (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside) radius)
  translatedTaylorMajorantIsCauchy coefficients outer witness center inside radius nonnegative strict =
    Real.uniformlyCauchyPointwiseLimitIsCauchy
      (λ count → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
      (complexPowerSeriesMajorant (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside) radius)
      (finiteTranslatedMajorantsUniformlyCauchy coefficients outer witness center radius nonnegative strict)
      (λ order → mulPresIsLimitSequence (normℂ-preservesLimit
        (finiteTranslatedCoefficientℂLimit coefficients outer witness center inside order))
        (constantIsLimitSequence (powℝ radius order)))
