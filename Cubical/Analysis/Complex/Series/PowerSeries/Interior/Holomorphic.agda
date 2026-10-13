module Cubical.Analysis.Complex.Series.PowerSeries.Interior.Holomorphic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Density
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.InteriorConvergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace
open import Cubical.Analysis.Complex.Calculus.Holomorphic

-- The derivative value and its series representation are constructed
-- together. Uniqueness makes this package a proposition, so one may use a
-- truncated intermediate radius without choosing a radius for every point.
ComplexPowerSeriesDerivativeSumAt : ComplexSequence → (ℂ → ℂ) → ℂ → Type₀
ComplexPowerSeriesDerivativeSumAt coefficients function z = Σ[ value ∈ ℂ ]
  HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) z) value
    × IsComplexDerivativeAt function value z

isPropComplexPowerSeriesDerivativeSumAt : ∀ coefficients function z →
  isProp (ComplexPowerSeriesDerivativeSumAt coefficients function z)
isPropComplexPowerSeriesDerivativeSumAt coefficients function z (v , vs , vd) (w , ws , wd) =
  Σ≡Prop (λ value → isProp× (isPropHasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) z) value)
    (isPropIsComplexDerivativeAlongAt (ℂPremetricSpace .snd) (idfun ℂ) function value z))
    (complexSumUnique (powerSeriesTermsℂ (formalDerivativeℂ coefficients) z) v w vs ws)

opaque
  complexPowerSeriesConstructDerivativeAtInterior : ∀ coefficients outer (function : ℂ → ℂ) →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    (∀ z → normℂ z <ℝ outer → HasComplexSum (powerSeriesTermsℂ coefficients z) (function z)) →
    ∀ z → normℂ z <ℝ outer → ComplexPowerSeriesDerivativeSumAt coefficients function z
  complexPowerSeriesConstructDerivativeAtInterior coefficients outer function witness sums z inside =
    PT.rec (isPropComplexPowerSeriesDerivativeSumAt coefficients function z)
      (λ { (q , below , above) → atRadius (rat q) below above }) (denseℚinℝ (normℂ z) outer inside)
    where
    atRadius : ∀ inner → normℂ z <ℝ inner → inner <ℝ outer → ComplexPowerSeriesDerivativeSumAt coefficients function z
    atRadius inner below above = d (z , below) , derivativeSum (z , below) ,
      openSubspaceComplexDerivativeAtWithExtension (OpenComplexNormRadiusPredicate inner)
        (openComplexNormRadiusIsOpen inner) (function ∘ fst) d function
        (complexPowerSeriesHasFormalDerivativeAlong (OpenComplexNormRadiusPremetricSpace inner .snd)
          fst (function ∘ fst) d coefficients inner bounded derivativeWitness
          (snd (NE→C (openComplexNormRadiusInclusionNE inner)))
          (λ point → sums (fst point) (<ℝ-trans (normℂ (fst point)) inner outer (snd point) above)) derivativeSum)
        (λ _ → refl) z below
      where
      bounded : ∀ (point : OpenComplexNormRadius inner) → normℂ (fst point) ≤ℝ inner
      bounded point = <ℝ-weaken (normℂ (fst point)) inner (snd point)

      derivativeWitness : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients inner)
      derivativeWitness = complexPowerSeriesDerivativeMajorantIsCauchyAtInterior coefficients inner outer
        (≤ℝ-trans 0ℝ (normℂ z) inner (normℂ-nonnegative z) (<ℝ-weaken (normℂ z) inner below)) above witness

      d : OpenComplexNormRadius inner → ℂ
      d = formalDerivativeℂValue coefficients fst inner bounded derivativeWitness

      derivativeSum : ∀ point → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (fst point)) (d point)
      derivativeSum = formalDerivativeℂValueHasSum coefficients fst inner bounded derivativeWitness

-- Only original sums are supplied. Derivative values and derivative-series
-- sums follow from the single native norm-majorant witness at the outer radius.
complexPowerSeriesIsHolomorphicOnInterior : ∀ coefficients outer (function : ℂ → ℂ) →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
  (∀ z → normℂ z <ℝ outer → HasComplexSum (powerSeriesTermsℂ coefficients z) (function z)) →
  IsHolomorphicOn (λ z → normℂ z <ℝ outer) function
complexPowerSeriesIsHolomorphicOnInterior coefficients outer function witness sums z inside =
  let result = complexPowerSeriesConstructDerivativeAtInterior coefficients outer function witness sums z inside
  in fst result , snd (snd result)
