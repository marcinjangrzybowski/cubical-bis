module Cubical.Analysis.Complex.Series.Geometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Functions.Powers
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Geometric.Real as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polynomial.Expansion.Modulus using (modulusℂ-power)
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
import Cubical.Analysis.Complex.Series.Geometric.Algebra as Algebra

private module A = Algebra.GeometricAlgebra ℂCommRing

geometricTermsℂ : ℂ → ComplexSequence
geometricTermsℂ z n = z ^ℂ n

opaque
  geometricPartialSumℂ : ∀ z n → (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTermsℂ z) n ≡ 1ℂ -ℂ (z ^ℂ n)
  geometricPartialSumℂ z = A.partialSumIdentity z (partialSumℂ (geometricTermsℂ z))
    (partialSumℂ-zero (geometricTermsℂ z)) (partialSumℂ-step (geometricTermsℂ z))

opaque
  -- This uses the Euclidean unit disk, not just the smaller l1 unit ball.
  -- Exact multiplicativity of the existing modulus supplies both bounds.
  geometricComplexSeriesIsAbsolutelyCauchy : ∀ z → modulusℂ z <ℝ 1ℝ →
    IsComplexAbsolutelyCauchySeries (geometricTermsℂ z)
  geometricComplexSeriesIsAbsolutelyCauchy z inside =
    coordinatesComplexAbsolutelyCauchy (geometricTermsℂ z)
      (Real.dominatedCauchySeriesIsCauchy (absℝ ∘ re ∘ geometricTermsℂ z) (powℝ (modulusℂ z))
        (λ n → subst2 _≤ℝ_ (sym (absIdem (re (z ^ℂ n)))) (modulusℂ-power z n)
          (reAbs≤modulusℂ (z ^ℂ n))) majorant)
      (Real.dominatedCauchySeriesIsCauchy (absℝ ∘ im ∘ geometricTermsℂ z) (powℝ (modulusℂ z))
        (λ n → subst2 _≤ℝ_ (sym (absIdem (im (z ^ℂ n)))) (modulusℂ-power z n)
          (imAbs≤modulusℂ (z ^ℂ n))) majorant)
    where
    majorant : Real.IsCauchySeries (powℝ (modulusℂ z))
    majorant = Real.realGeometricSeriesIsCauchy (modulusℂ z)
      (subst (_<ℝ 1ℝ) (sym (absOfNonnegative (modulusℂ z) (modulusℂ-nonnegative z))) inside)

geometricComplexSeriesIsCauchy : ∀ z → modulusℂ z <ℝ 1ℝ → IsComplexCauchySeries (geometricTermsℂ z)
geometricComplexSeriesIsCauchy z inside = absoluteComplexCauchySeriesIsCauchy (geometricTermsℂ z)
  (geometricComplexSeriesIsAbsolutelyCauchy z inside)

geometricComplexSeriesAbsolutelySummable : ∀ z → modulusℂ z <ℝ 1ℝ → ComplexAbsolutelySummable (geometricTermsℂ z)
geometricComplexSeriesAbsolutelySummable z inside = absoluteComplexCauchySeriesIsAbsolutelySummable (geometricTermsℂ z)
  (geometricComplexSeriesIsAbsolutelyCauchy z inside)

geometricComplexSeriesSummable : ∀ z → modulusℂ z <ℝ 1ℝ → ComplexSummable (geometricTermsℂ z)
geometricComplexSeriesSummable z inside = complexCauchySeriesIsSummable (geometricTermsℂ z)
  (geometricComplexSeriesIsCauchy z inside)

opaque
  -- Every supplied geometric sum is an inverse of 1-z. Existence on the
  -- unit disk is the preceding theorem; no quotient or apartness choice is
  -- needed to state this exact identity.
  geometricComplexSumLaw : ∀ z (summed : ComplexSummable (geometricTermsℂ z)) →
    (1ℂ -ℂ z) ·ℂ seriesSumℂ (geometricTermsℂ z) summed ≡ 1ℂ
  geometricComplexSumLaw z summed = complexLimitUnique
    (λ n → (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTermsℂ z) n)
    ((1ℂ -ℂ z) ·ℂ seriesSumℂ (geometricTermsℂ z) summed) 1ℂ
    (mulComplexLimit (constantComplexLimit (1ℂ -ℂ z)) (snd summed))
    (subst (λ s → IsComplexLimit s 1ℂ) (sym (funExt (geometricPartialSumℂ z)))
      (subst (IsComplexLimit (λ n → 1ℂ -ℂ (z ^ℂ n))) (cong (1ℂ +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR 1ℂ)
        (subComplexLimit (constantComplexLimit 1ℂ) (complexSummableTermsTendToZero (geometricTermsℂ z) summed))))
