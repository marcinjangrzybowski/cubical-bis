module Cubical.Analysis.Complex.Series.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
import Cubical.Analysis.Real.Sequence as Real
import Cubical.Analysis.Real.Base as Real
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative)
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Tails as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Bounds
open import Cubical.Analysis.Complex.Series.Tails

-- Absolute convergence is measured by the existing l1 norm. Ordinary
-- summability and a native Cauchy witness are deliberately separate inputs.
ComplexAbsolutelySummable : ComplexSequence → Type₀
ComplexAbsolutelySummable terms = Real.Summable (normℂ ∘ terms)

IsComplexAbsolutelyCauchySeries : ComplexSequence → Type₀
IsComplexAbsolutelyCauchySeries terms = Real.IsCauchySeries (normℂ ∘ terms)

isPropComplexAbsolutelySummable : ∀ terms → isProp (ComplexAbsolutelySummable terms)
isPropComplexAbsolutelySummable terms = Real.isPropSummable (normℂ ∘ terms)

isPropIsComplexAbsolutelyCauchySeries : ∀ terms → isProp (IsComplexAbsolutelyCauchySeries terms)
isPropIsComplexAbsolutelyCauchySeries terms = Real.isPropIsCauchySeries (normℂ ∘ terms)

opaque
  dominatedComplexSeriesIsCauchy : ∀ terms bound → (∀ n → normℂ (terms n) ≤ℝ bound n) →
    Real.IsCauchySeries bound → IsComplexCauchySeries terms
  dominatedComplexSeriesIsCauchy terms bound dominates witness =
    Real.dominatedCauchySeriesIsCauchy (re ∘ terms) bound
      (λ n → ≤ℝ-trans (absℝ (re (terms n))) (normℂ (terms n)) (bound n) (reAbs≤normℂ (terms n)) (dominates n)) witness ,
    Real.dominatedCauchySeriesIsCauchy (im ∘ terms) bound
      (λ n → ≤ℝ-trans (absℝ (im (terms n))) (normℂ (terms n)) (bound n) (imAbs≤normℂ (terms n)) (dominates n)) witness

dominatedComplexSeriesIsSummable : ∀ terms bound → (∀ n → normℂ (terms n) ≤ℝ bound n) →
  Real.IsCauchySeries bound → ComplexSummable terms
dominatedComplexSeriesIsSummable terms bound dominates witness =
  complexCauchySeriesIsSummable terms (dominatedComplexSeriesIsCauchy terms bound dominates witness)

opaque
  dominatedComplexSeriesIsAbsolutelyCauchy : ∀ terms bound → (∀ n → normℂ (terms n) ≤ℝ bound n) →
    Real.IsCauchySeries bound → IsComplexAbsolutelyCauchySeries terms
  dominatedComplexSeriesIsAbsolutelyCauchy terms bound dominates =
    Real.dominatedCauchySeriesIsCauchy (normℂ ∘ terms) bound
      (λ n → subst (_≤ℝ bound n) (sym (absOfNonnegative (normℂ (terms n)) (normℂ-nonnegative (terms n)))) (dominates n))

-- Absolute native convergence is equivalent to absolute native convergence
-- of both coordinates. Both directions preserve supplied global witnesses.
opaque
  absoluteComplexCauchyCoordinates : ∀ terms → IsComplexAbsolutelyCauchySeries terms →
    Real.IsAbsolutelyCauchySeries (re ∘ terms) × Real.IsAbsolutelyCauchySeries (im ∘ terms)
  absoluteComplexCauchyCoordinates terms witness =
    Real.dominatedCauchySeriesIsCauchy (absℝ ∘ re ∘ terms) (normℂ ∘ terms)
      (λ n → subst (_≤ℝ normℂ (terms n)) (sym (absIdem (re (terms n)))) (reAbs≤normℂ (terms n))) witness ,
    Real.dominatedCauchySeriesIsCauchy (absℝ ∘ im ∘ terms) (normℂ ∘ terms)
      (λ n → subst (_≤ℝ normℂ (terms n)) (sym (absIdem (im (terms n)))) (imAbs≤normℂ (terms n))) witness

  coordinatesComplexAbsolutelyCauchy : ∀ terms →
    Real.IsAbsolutelyCauchySeries (re ∘ terms) → Real.IsAbsolutelyCauchySeries (im ∘ terms) →
    IsComplexAbsolutelyCauchySeries terms
  coordinatesComplexAbsolutelyCauchy terms real imaginary =
    subst Real.SeqWitness (sym (funExt (Real.partialSum-add (absℝ ∘ re ∘ terms) (absℝ ∘ im ∘ terms))))
      (Real.addSeqWitness real imaginary)

  complexNormSeriesIsAbsolutelyCauchy : ∀ terms → IsComplexAbsolutelyCauchySeries terms →
    Real.IsAbsolutelyCauchySeries (normℂ ∘ terms)
  complexNormSeriesIsAbsolutelyCauchy terms = subst Real.IsCauchySeries
    (sym (funExt (λ n → absOfNonnegative (normℂ (terms n)) (normℂ-nonnegative (terms n)))))

absoluteComplexCauchySeriesIsCauchy : ∀ terms → IsComplexAbsolutelyCauchySeries terms → IsComplexCauchySeries terms
absoluteComplexCauchySeriesIsCauchy terms = dominatedComplexSeriesIsCauchy terms (normℂ ∘ terms)
  (λ n → ≤ℝ-refl (normℂ (terms n)))

absoluteComplexCauchySeriesIsSummable : ∀ terms → IsComplexAbsolutelyCauchySeries terms → ComplexSummable terms
absoluteComplexCauchySeriesIsSummable terms witness =
  complexCauchySeriesIsSummable terms (absoluteComplexCauchySeriesIsCauchy terms witness)

absoluteComplexCauchySeriesIsAbsolutelySummable : ∀ terms → IsComplexAbsolutelyCauchySeries terms → ComplexAbsolutelySummable terms
absoluteComplexCauchySeriesIsAbsolutelySummable terms = Real.cauchySeriesIsSummable (normℂ ∘ terms)

seriesSumℂNormBound : ∀ terms (summed : ComplexSummable terms) (absolute : ComplexAbsolutelySummable terms) →
  normℂ (seriesSumℂ terms summed) ≤ℝ Real.seriesSum (normℂ ∘ terms) absolute
seriesSumℂNormBound terms summed absolute = seriesSumℂBoundBy terms (normℂ ∘ terms) summed absolute
  (λ n → ≤ℝ-refl (normℂ (terms n)))

dropComplexSeriesAbsolutelyCauchy : ∀ start terms → IsComplexAbsolutelyCauchySeries terms →
  IsComplexAbsolutelyCauchySeries (dropComplexSeries start terms)
dropComplexSeriesAbsolutelyCauchy start terms = Real.dropSeriesIsCauchy start (normℂ ∘ terms)

-- A quantitative remainder bound from any supplied summable majorant.
-- Existence of the complex sum can separately be obtained from Cauchy data.
opaque
  seriesSumℂRemainderBound : ∀ terms bound (summed : ComplexSummable terms) (majorant : Real.Summable bound) →
    (∀ n → normℂ (terms n) ≤ℝ bound n) → ∀ start →
    normℂ (seriesSumℂ terms summed -ℂ partialSumℂ terms start) ≤ℝ
      Real.seriesSum (Real.dropSeries start bound) (Real.dropSeriesSummable start bound majorant)
  seriesSumℂRemainderBound terms bound summed majorant dominates start =
    seriesSumℂBoundBy (dropComplexSeries start terms) (Real.dropSeries start bound)
      (dropComplexSeriesSummable start terms summed) (Real.dropSeriesSummable start bound majorant)
      (λ n → dominates (n ℕ.+ start))
