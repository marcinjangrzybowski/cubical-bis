module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Tails as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Representation

-- Uniform representation and an actual summable-tail remainder on every
-- closed translated radius strictly contained in the original outer ball.
module _ (coefficients : ComplexSequence) (outer : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (center : ℂ) (inside : normℂ center <ℝ outer) (radius : ℝ)
  (nonnegative : 0ℝ ≤ℝ radius) (strict : normℂ center + radius <ℝ outer) where
  private
    translated : ComplexSequence
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside

    native : Real.IsCauchySeries (complexPowerSeriesMajorant translated radius)
    native = translatedTaylorMajorantIsCauchy coefficients outer witness center inside radius nonnegative strict

    majorantSum : Real.Summable (complexPowerSeriesMajorant translated radius)
    majorantSum = Real.cauchySeriesIsSummable (complexPowerSeriesMajorant translated radius) native

    representation : ∀ increment → normℂ increment ≤ℝ radius → ∀ value →
      HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ increment)) value →
      HasComplexSum (powerSeriesTermsℂ translated increment) value
    representation increment bounded = translatedTaylorHasSum coefficients outer witness center inside increment
      (≤<ℝ-trans (normℂ center + normℂ increment) (normℂ center + radius) outer
        (addPres≤L (normℂ increment) radius (normℂ center) bounded) strict)

  opaque
    translatedTaylorUniformHasSum : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℂ)
      (bounded : ∀ point → normℂ (coordinate point) ≤ℝ radius) value →
      (∀ point → HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ coordinate point)) (value point)) →
      UniformHasComplexSum (λ point → powerSeriesTermsℂ translated (coordinate point)) value
    translatedTaylorUniformHasSum coordinate bounded value originalSums =
      subst (UniformHasComplexSum (λ point → powerSeriesTermsℂ translated (coordinate point)))
        (funExt λ point → complexSumUnique (powerSeriesTermsℂ translated (coordinate point))
          (uniformComplexPowerSeriesValue coordinate translated radius bounded native point) (value point)
          (uniformHasComplexSumAt (uniformComplexPowerSeriesHasSum coordinate translated radius bounded native) point)
          (representation (coordinate point) (bounded point) (value point) (originalSums point)))
        (uniformComplexPowerSeriesHasSum coordinate translated radius bounded native)

    translatedTaylorRemainderBound : ∀ increment → normℂ increment ≤ℝ radius → ∀ value →
      HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ increment)) value → ∀ count →
      normℂ (value -ℂ partialSumℂ (powerSeriesTermsℂ translated increment) count)
        ≤ℝ Real.seriesSum (Real.dropSeries count (complexPowerSeriesMajorant translated radius))
          (Real.dropSeriesSummable count (complexPowerSeriesMajorant translated radius) majorantSum)
    translatedTaylorRemainderBound increment bounded value originalSum count =
      seriesSumℂRemainderBound (powerSeriesTermsℂ translated increment) (complexPowerSeriesMajorant translated radius)
        (value , representation increment bounded value originalSum) majorantSum
        (complexPowerSeriesTermBound translated increment radius bounded) count
