module Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
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
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Convergence
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Continuity
open import Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower

-- Canonical derivative values on the entire open convergence ball. At each
-- point the radius norm(z) is explicit, so all orders have native convergence
-- data from the one supplied outer witness. Local differentiability uses one
-- truncated intermediate radius, eliminated into a proposition.
module _ coefficients outer
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer)) where
  private
    domain : PremetricSpace ℓ-zero ℓ-zero
    domain = OpenComplexNormRadiusPremetricSpace outer

    derivativeSummable : ∀ order (point : fst domain) →
      ComplexSummable (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (fst point))
    derivativeSummable order point = complexPowerSeriesSummableOn (repeatedFormalDerivativeℂ order coefficients)
      (normℂ (fst point))
      (repeatedComplexMajorantIsCauchyAtInterior order coefficients (normℂ (fst point)) outer
        (normℂ-nonnegative (fst point)) (snd point) witness)
      (fst point) (≤ℝ-refl (normℂ (fst point)))

  -- Keep the completion construction abstract when clients compare values.
  opaque
    openInteriorPowerSeriesDerivatives : ℕ → OpenComplexNormRadius outer → ℂ
    openInteriorPowerSeriesDerivatives order point = fst (derivativeSummable order point)

    openInteriorPowerSeriesDerivativeSums : ∀ order point →
      HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (fst point))
        (openInteriorPowerSeriesDerivatives order point)
    openInteriorPowerSeriesDerivativeSums order point = snd (derivativeSummable order point)

  openInteriorPowerSeriesDerivativeAgrees : ∀ order point value →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (fst point)) value →
    openInteriorPowerSeriesDerivatives order point ≡ value
  openInteriorPowerSeriesDerivativeAgrees order point value = complexSumUnique
    (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients) (fst point))
    (openInteriorPowerSeriesDerivatives order point) value (openInteriorPowerSeriesDerivativeSums order point)

  opaque
    openInteriorPowerSeriesDerivativeTower : IsComplexDerivativeTowerAlong
      (snd domain) fst openInteriorPowerSeriesDerivatives
    openInteriorPowerSeriesDerivativeTower order point = PT.rec
      (isPropIsComplexDerivativeAlongAt (snd domain) fst (openInteriorPowerSeriesDerivatives order)
        (openInteriorPowerSeriesDerivatives (suc order) point) point)
      (λ { (q , below , above) → atRadius (rat q) below above })
      (denseℚinℝ (normℂ (fst point)) outer (snd point))
      where
      atRadius : ∀ inner → normℂ (fst point) <ℝ inner → inner <ℝ outer →
        IsComplexDerivativeAlongAt (snd domain) fst (openInteriorPowerSeriesDerivatives order)
          (openInteriorPowerSeriesDerivatives (suc order) point) point
      atRadius inner below above = openSubspaceComplexDerivativeAlongValueAtWithExtension
        (snd domain) fst predicate openPredicate
        (openInteriorPowerSeriesDerivatives order ∘ fst) (openInteriorPowerSeriesDerivatives order)
        (openInteriorPowerSeriesDerivatives (suc order) point) point below
        (complexPowerSeriesHasFormalDerivativeAlong (snd smaller) (fst ∘ fst)
          (openInteriorPowerSeriesDerivatives order ∘ fst) (openInteriorPowerSeriesDerivatives (suc order) ∘ fst)
          (repeatedFormalDerivativeℂ order coefficients) inner bounded derivativeWitness
          (snd (NE→C coordinateNE)) (openInteriorPowerSeriesDerivativeSums order ∘ fst) derivativeSum (point , below))
        (λ _ → refl)
        where
        predicate : ℙ (fst domain)
        predicate = predicatePreimage fst (OpenComplexNormRadiusPredicate inner)

        openPredicate : IsOpenPredicate (snd domain) predicate
        openPredicate = continuousPreimageIsOpen fst (OpenComplexNormRadiusPredicate inner)
          (snd (NE→C (openComplexNormRadiusInclusionNE outer))) (openComplexNormRadiusIsOpen inner)

        smaller : PremetricSpace ℓ-zero ℓ-zero
        smaller = PremetricSubspace domain predicate

        coordinateNE : NE[ smaller , ℂPremetricSpace ]
        fst coordinateNE = fst ∘ fst
        IsNonExpanding.pres≈ (snd coordinateNE) _ _ _ close = close

        bounded : ∀ (p : fst smaller) → normℂ (fst (fst p)) ≤ℝ inner
        bounded p = <ℝ-weaken (normℂ (fst (fst p))) inner (snd p)

        derivativeWitness : Real.IsCauchySeries
          (complexPowerSeriesDerivativeMajorant (repeatedFormalDerivativeℂ order coefficients) inner)
        derivativeWitness = subst Real.IsCauchySeries (repeatedDerivativeMajorant-successor order coefficients inner)
          (repeatedComplexMajorantIsCauchyAtInterior (suc order) coefficients inner outer
            (≤ℝ-trans 0ℝ (normℂ (fst point)) inner (normℂ-nonnegative (fst point))
              (<ℝ-weaken (normℂ (fst point)) inner below)) above witness)

        derivativeSum : ∀ (p : fst smaller) →
          HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ (repeatedFormalDerivativeℂ order coefficients)) (fst (fst p)))
            (openInteriorPowerSeriesDerivatives (suc order) (fst p))
        derivativeSum p = subst
          (λ a → HasComplexSum (powerSeriesTermsℂ a (fst (fst p))) (openInteriorPowerSeriesDerivatives (suc order) (fst p)))
          (repeatedFormalDerivativeℂ-successor order coefficients) (openInteriorPowerSeriesDerivativeSums (suc order) (fst p))

  openInteriorPowerSeriesDerivativeIsContinuous : ∀ order →
    isContinuous (snd domain) (openInteriorPowerSeriesDerivatives order) (ℂPremetricSpace .snd)
  openInteriorPowerSeriesDerivativeIsContinuous order point = complexDerivativeAlongAtIsContinuous
    (snd domain) fst (openInteriorPowerSeriesDerivatives order) (openInteriorPowerSeriesDerivatives (suc order) point) point
    (snd (NE→C (openComplexNormRadiusInclusionNE outer)) point) (openInteriorPowerSeriesDerivativeTower order point)
