module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Interior
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower.OpenSubspace

-- Coefficient recovery is intrinsic to the represented function. A supplied
-- derivative tower agrees with the tower constructed from convergence; no
-- identities between the supplied derivatives and formal series are assumed.
module _ coefficients inner outer (positive : 0ℝ <ℝ inner) (strict : inner <ℝ outer)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer)) where
  private
    origin : OpenComplexNormRadius inner
    origin = interiorTaylorOrigin coefficients inner outer positive strict witness

  opaque
    complexPowerSeriesTaylorCoefficientsOfTower :
      (derivatives : ℕ → OpenComplexNormRadius inner → ℂ) →
      IsComplexDerivativeTowerAlong (OpenComplexNormRadiusPremetricSpace inner .snd) fst derivatives →
      (∀ point → HasComplexSum (powerSeriesTermsℂ coefficients (fst point)) (derivatives zero point)) →
      taylorCoefficientsℂ (λ n → derivatives n origin) ≡ coefficients
    complexPowerSeriesTaylorCoefficientsOfTower derivatives tower sums =
      cong (λ D → taylorCoefficientsℂ (λ n → D n origin)) (sym towersAgree)
        ∙ interiorTaylorCoefficients coefficients inner outer positive strict witness
      where
      canonical : ℕ → OpenComplexNormRadius inner → ℂ
      canonical = interiorPowerSeriesDerivatives coefficients inner outer positive strict witness

      towersAgree : canonical ≡ derivatives
      towersAgree = openSubspaceComplexDerivativeTowerUnique (OpenComplexNormRadiusPredicate inner)
        (openComplexNormRadiusIsOpen inner) canonical derivatives
        (interiorPowerSeriesDerivativeTower coefficients inner outer positive strict witness) tower
        (funExt λ point → complexSumUnique (powerSeriesTermsℂ coefficients (fst point))
          (canonical zero point) (derivatives zero point)
          (interiorPowerSeriesDerivativeSums coefficients inner outer positive strict witness zero point) (sums point))

-- Two convergent expansions of the same local function have the same
-- coefficients. The outer radii and native convergence witnesses may differ;
-- agreement is needed only on the common positive open inner ball.
opaque
  localComplexPowerSeriesCoefficientsUnique : ∀ first second inner firstOuter secondOuter →
    (positive : 0ℝ <ℝ inner) → inner <ℝ firstOuter → inner <ℝ secondOuter →
    Real.IsCauchySeries (complexPowerSeriesMajorant first firstOuter) →
    Real.IsCauchySeries (complexPowerSeriesMajorant second secondOuter) →
    (function : OpenComplexNormRadius inner → ℂ) →
    (∀ point → HasComplexSum (powerSeriesTermsℂ first (fst point)) (function point)) →
    (∀ point → HasComplexSum (powerSeriesTermsℂ second (fst point)) (function point)) →
    first ≡ second
  localComplexPowerSeriesCoefficientsUnique first second inner firstOuter secondOuter positive
    firstStrict secondStrict firstWitness secondWitness function firstSums secondSums =
    sym (interiorTaylorCoefficients first inner firstOuter positive firstStrict firstWitness)
      ∙ complexPowerSeriesTaylorCoefficientsOfTower second inner secondOuter positive secondStrict secondWitness
          canonical (interiorPowerSeriesDerivativeTower first inner firstOuter positive firstStrict firstWitness)
          (λ point → subst (HasComplexSum (powerSeriesTermsℂ second (fst point)))
            (sym (agrees point)) (secondSums point))
    where
    canonical : ℕ → OpenComplexNormRadius inner → ℂ
    canonical = interiorPowerSeriesDerivatives first inner firstOuter positive firstStrict firstWitness

    agrees : ∀ point → canonical zero point ≡ function point
    agrees point = complexSumUnique (powerSeriesTermsℂ first (fst point)) (canonical zero point) (function point)
      (interiorPowerSeriesDerivativeSums first inner firstOuter positive firstStrict firstWitness zero point) (firstSums point)
