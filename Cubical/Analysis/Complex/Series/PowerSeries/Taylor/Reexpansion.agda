module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Reexpansion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Domain.Radius.Translation
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Uniqueness
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Calculus.Derivative.Translation

-- Uniqueness/identification of a supplied reexpansion. The representation
-- premise below identifies an arbitrary supplied coefficient sequence.
-- Translation.Convergence and Translation.Representation independently
-- construct convergence and representation for the canonical coefficients.
module _ original outer
  (originalWitness : Real.IsCauchySeries (complexPowerSeriesMajorant original outer))
  reexpanded reexpandedOuter
  (reexpandedWitness : Real.IsCauchySeries (complexPowerSeriesMajorant reexpanded reexpandedOuter))
  inner (positive : 0ℝ <ℝ inner) (strict : inner <ℝ reexpandedOuter)
  center (fits : normℂ center + inner ≤ℝ outer) where
  private
    origin : OpenComplexNormRadius inner
    origin = interiorTaylorOrigin reexpanded inner reexpandedOuter positive strict reexpandedWitness

    translation : OpenComplexNormRadius inner → OpenComplexNormRadius outer
    translation = translateOpenComplexNormRadius center inner outer fits

  reexpansionCenterInside : normℂ center <ℝ outer
  reexpansionCenterInside = subst (λ z → normℂ z <ℝ outer) (+ℂIdR center) (snd (translation origin))

  reexpansionDerivativeTowerValues : ℕ → OpenComplexNormRadius inner → ℂ
  reexpansionDerivativeTowerValues n point = openInteriorPowerSeriesDerivatives original outer originalWitness n (translation point)

  reexpansionDerivativeTower : IsComplexDerivativeTowerAlong
    (OpenComplexNormRadiusPremetricSpace inner .snd) fst reexpansionDerivativeTowerValues
  reexpansionDerivativeTower n point = untranslateComplexDerivativeCoordinateAlongAt
    (OpenComplexNormRadiusPremetricSpace inner .snd) fst (reexpansionDerivativeTowerValues n) center
    (reexpansionDerivativeTowerValues (suc n) point) point
    (pullbackComplexDerivativeAlong (OpenComplexNormRadiusPremetricSpace inner .snd)
      (OpenComplexNormRadiusPremetricSpace outer .snd) fst
      (openInteriorPowerSeriesDerivatives original outer originalWitness n)
      (openInteriorPowerSeriesDerivatives original outer originalWitness (suc n)) translation
      (snd (NE→C (translateOpenComplexNormRadiusNE center inner outer fits)))
      (openInteriorPowerSeriesDerivativeTower original outer originalWitness n) point)

  opaque
    complexPowerSeriesReexpansionCoefficients :
      (∀ point → HasComplexSum (powerSeriesTermsℂ reexpanded (fst point)) (reexpansionDerivativeTowerValues zero point)) →
      reexpanded ≡ complexPowerSeriesTaylorCoefficientsAtCenter original outer originalWitness center reexpansionCenterInside
    complexPowerSeriesReexpansionCoefficients representation =
      sym (complexPowerSeriesTaylorCoefficientsOfTower reexpanded inner reexpandedOuter positive strict reexpandedWitness
        reexpansionDerivativeTowerValues reexpansionDerivativeTower representation)
      ∙ cong (λ point → taylorCoefficientsℂ (λ n → openInteriorPowerSeriesDerivatives original outer originalWitness n point))
          (Σ≡Prop (λ z → isProp<ℝ (normℂ z) outer) (+ℂIdR center))
