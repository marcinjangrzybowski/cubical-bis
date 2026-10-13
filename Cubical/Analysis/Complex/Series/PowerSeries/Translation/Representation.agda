module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Representation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as Nat
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.FiniteSupport
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PointwiseLimit
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Approximation
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence

private module R = Ring.RingTheory (CommRing→Ring ℂCommRing)

opaque
  finiteTranslatedPowerSeriesHasSum : ∀ coefficients center increment count →
    HasComplexSum (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment)
      (partialSumℂ (powerSeriesTermsℂ coefficients (center +ℂ increment)) count)
  finiteTranslatedPowerSeriesHasSum coefficients center increment count =
    subst (HasComplexSum (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment))
      (finitePowerSeriesTranslationℂ coefficients center increment count)
      (finiteSupportHasComplexSum (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment)
        count vanishes)
    where
    vanishes : ∀ order → count Nat.≤ order →
      powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment order ≡ 0ℂ
    vanishes order late = cong (λ n → partialSumℂ (translatedCoefficientTermsℂ coefficients center order) n ·ℂ (increment ^ℂ order))
      (Nat.n∸m≡0 count order late) ∙ R.0LeftAnnihilates (increment ^ℂ order)

-- General reexpansion of a supplied native power series about an interior
-- center. The coefficients are the actual normalized derivatives, and the
-- represented value is the original sum. The l1 radius is the native norm
-- used throughout Complex; no Euclidean-norm or HIT-real comparison is used.
opaque
  translatedTaylorHasSum : ∀ (coefficients : ComplexSequence) (outer : ℝ)
    (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
    (center : ℂ) (inside : normℂ center <ℝ outer) increment →
    normℂ center + normℂ increment <ℝ outer → ∀ value →
    HasComplexSum (powerSeriesTermsℂ coefficients (center +ℂ increment)) value →
    HasComplexSum (powerSeriesTermsℂ
      (complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside) increment) value
  translatedTaylorHasSum coefficients outer witness center inside increment strict value originalSum =
    finish (complexPowerSeriesSummableOn translated (normℂ increment)
      (translatedTaylorMajorantIsCauchy coefficients outer witness center inside (normℂ increment)
        (normℂ-nonnegative increment) strict) increment (≤ℝ-refl (normℂ increment)))
    where
    translated : ComplexSequence
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside

    approximations : ℕ → ComplexSequence
    approximations count = powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment

    originalPartialSums : ComplexSequence
    originalPartialSums = partialSumℂ (powerSeriesTermsℂ coefficients (center +ℂ increment))

    uniform : UniformlyComplexCauchySeries ℕ approximations
    uniform = finiteTranslatedPowerSeriesUniformlyCauchy coefficients outer witness center (normℂ increment)
      (normℂ-nonnegative increment) strict increment (≤ℝ-refl (normℂ increment))

    uniformSums : UniformHasComplexSum approximations originalPartialSums
    uniformSums = subst (UniformHasComplexSum approximations)
      (funExt λ count → uniformComplexSeriesValueAgrees approximations uniform count
        (originalPartialSums count , finiteTranslatedPowerSeriesHasSum coefficients center increment count))
      (uniformlyComplexCauchySeriesHasUniformSum approximations uniform)

    termLimits : ∀ order → IsComplexLimit (λ count → approximations count order)
      (powerSeriesTermsℂ translated increment order)
    termLimits order = mulComplexLimit (finiteTranslatedCoefficientℂLimit coefficients outer witness center inside order)
      (constantComplexLimit (increment ^ℂ order))

    finish : ComplexSummable (powerSeriesTermsℂ translated increment) →
      HasComplexSum (powerSeriesTermsℂ translated increment) value
    finish (translatedValue , translatedSum) = subst (HasComplexSum (powerSeriesTermsℂ translated increment))
      (complexLimitUnique originalPartialSums translatedValue value
        (uniformComplexSeriesSumsPresPointwiseLimit approximations (powerSeriesTermsℂ translated increment)
          originalPartialSums translatedValue uniformSums termLimits translatedSum) originalSum)
      translatedSum
