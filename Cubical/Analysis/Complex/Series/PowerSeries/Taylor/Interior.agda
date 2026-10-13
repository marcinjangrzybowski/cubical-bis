module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Interior where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Tails as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Tower
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower

-- Taylor representation for a supplied convergent power series on its
-- intrinsic open norm ball. This does not assume that an arbitrary
-- holomorphic function already has a power-series representation.
module _ (coefficients : ComplexSequence) (inner outer : ℝ)
  (positive : 0ℝ <ℝ inner) (strict : inner <ℝ outer)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer)) where
  private
    nonnegative : 0ℝ ≤ℝ inner
    nonnegative = <ℝ-weaken 0ℝ inner positive
    bounded : ∀ (point : OpenComplexNormRadius inner) → normℂ (fst point) ≤ℝ inner
    bounded point = <ℝ-weaken (normℂ (fst point)) inner (snd point)

  interiorTaylorOrigin : OpenComplexNormRadius inner
  interiorTaylorOrigin = 0ℂ , subst (_<ℝ inner) (sym normℂ-zero) positive

  interiorPowerSeriesDerivatives : ℕ → OpenComplexNormRadius inner → ℂ
  interiorPowerSeriesDerivatives = complexHigherDerivativeValue fst coefficients inner outer nonnegative strict bounded witness

  interiorPowerSeriesDerivativeSums : ∀ n point →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n coefficients) (fst point))
      (interiorPowerSeriesDerivatives n point)
  interiorPowerSeriesDerivativeSums = complexHigherDerivativeHasSum fst coefficients inner outer nonnegative strict bounded witness

  interiorPowerSeriesDerivativeTower : IsComplexDerivativeTowerAlong
    (OpenComplexNormRadiusPremetricSpace inner .snd) fst interiorPowerSeriesDerivatives
  interiorPowerSeriesDerivativeTower = complexPowerSeriesHigherDerivativeTower
    fst coefficients inner outer nonnegative strict bounded witness (OpenComplexNormRadiusPremetricSpace inner .snd)
    (snd (NE→C (openComplexNormRadiusInclusionNE inner)))

  interiorTaylorCoefficients :
    taylorCoefficientsℂ (λ n → interiorPowerSeriesDerivatives n interiorTaylorOrigin) ≡ coefficients
  interiorTaylorCoefficients = complexPowerSeriesTaylorCoefficients coefficients
    (λ n → interiorPowerSeriesDerivatives n interiorTaylorOrigin) (λ n → interiorPowerSeriesDerivativeSums n interiorTaylorOrigin)

  interiorTaylorUniformHasSum : UniformHasComplexSum
    (λ point → powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → interiorPowerSeriesDerivatives n interiorTaylorOrigin)) (fst point))
    (interiorPowerSeriesDerivatives zero)
  interiorTaylorUniformHasSum = subst
    (λ c → UniformHasComplexSum (λ point → powerSeriesTermsℂ c (fst point)) (interiorPowerSeriesDerivatives zero))
    (sym interiorTaylorCoefficients)
    (complexHigherDerivativeUniformHasSum fst coefficients inner outer nonnegative strict bounded witness zero)

  private
    majorantSum : Real.Summable (complexPowerSeriesMajorant coefficients outer)
    majorantSum = Real.cauchySeriesIsSummable (complexPowerSeriesMajorant coefficients outer) witness

  -- The same supplied outer majorant controls the Taylor remainder. This is
  -- a tail of a native summable real series, not an unevaluated derivative
  -- bound or an additional convergence hypothesis.
  interiorTaylorRemainderBound : ∀ point count →
    normℂ (interiorPowerSeriesDerivatives zero point -ℂ partialSumℂ
      (powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → interiorPowerSeriesDerivatives n interiorTaylorOrigin)) (fst point)) count)
      ≤ℝ Real.seriesSum (Real.dropSeries count (complexPowerSeriesMajorant coefficients outer))
        (Real.dropSeriesSummable count (complexPowerSeriesMajorant coefficients outer) majorantSum)
  interiorTaylorRemainderBound point count = subst
    (λ c → normℂ (interiorPowerSeriesDerivatives zero point -ℂ partialSumℂ (powerSeriesTermsℂ c (fst point)) count)
      ≤ℝ Real.seriesSum (Real.dropSeries count (complexPowerSeriesMajorant coefficients outer))
        (Real.dropSeriesSummable count (complexPowerSeriesMajorant coefficients outer) majorantSum))
    (sym interiorTaylorCoefficients)
    (seriesSumℂRemainderBound (powerSeriesTermsℂ coefficients (fst point)) (complexPowerSeriesMajorant coefficients outer)
      (interiorPowerSeriesDerivatives zero point , interiorPowerSeriesDerivativeSums zero point) majorantSum
      (complexPowerSeriesTermBound coefficients (fst point) outer
        (<ℝ-weaken (normℂ (fst point)) outer (<ℝ-trans (normℂ (fst point)) inner outer (snd point) strict))) count)
