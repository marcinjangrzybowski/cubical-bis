module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
import Cubical.Data.Nat.Order as Nat
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative; 0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.RealScalar
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base

opaque
  formalPrimitiveℂWeightedNorm : ∀ constant coefficients n →
    normℂ (formalPrimitiveℂ constant coefficients (suc n)) · realNatural (suc n) ≡ normℂ (coefficients n)
  formalPrimitiveℂWeightedNorm constant coefficients n =
    cong (normℂ term ·_) (sym (absOfNonnegative (realNatural (suc n)) (realNatural-nonnegative (suc n))))
    ∙ sym (normℂ-multiplyReal term (realNatural (suc n)))
    ∙ cong normℂ (·ℂComm term (fromℝ (realNatural (suc n)))
      ∙ funExt⁻ (formalDerivativeℂ-formalPrimitiveℂ constant coefficients) n)
    where
    term : ℂ
    term = formalPrimitiveℂ constant coefficients (suc n)

  formalPrimitiveℂCoefficientBound : ∀ constant coefficients n →
    normℂ (formalPrimitiveℂ constant coefficients (suc n)) ≤ℝ normℂ (coefficients n)
  formalPrimitiveℂCoefficientBound constant coefficients n = subst2 _≤ℝ_
    (mulIdR (normℂ term)) (formalPrimitiveℂWeightedNorm constant coefficients n)
    (mulPres≤L 1ℝ (realNatural (suc n)) (normℂ term)
      (0≤→isNonnegative (normℂ term) (normℂ-nonnegative term)) (realNatural-mono (Nat.zero-<suc {n = n})))
    where
    term : ℂ
    term = formalPrimitiveℂ constant coefficients (suc n)

  -- This identity is stronger than merely inheriting interior convergence:
  -- the primitive's derivative majorant is the ORIGINAL radius majorant.
  formalPrimitiveℂDerivativeMajorant : ∀ constant coefficients radius →
    complexPowerSeriesDerivativeMajorant (formalPrimitiveℂ constant coefficients) radius ≡
      complexPowerSeriesMajorant coefficients radius
  formalPrimitiveℂDerivativeMajorant constant coefficients radius = funExt λ n →
    mulAssoc (normℂ (formalPrimitiveℂ constant coefficients (suc n))) (realNatural (suc n)) (powℝ radius n)
    ∙ cong (_· powℝ radius n) (formalPrimitiveℂWeightedNorm constant coefficients n)

  formalPrimitiveℂMajorantStepBound : ∀ constant coefficients radius → 0ℝ ≤ℝ radius → ∀ n →
    complexPowerSeriesMajorant (formalPrimitiveℂ constant coefficients) radius (suc n)
      ≤ℝ radius · complexPowerSeriesMajorant coefficients radius n
  formalPrimitiveℂMajorantStepBound constant coefficients radius nonnegative n = subst
    (complexPowerSeriesMajorant (formalPrimitiveℂ constant coefficients) radius (suc n) ≤ℝ_)
    (mulAssoc (normℂ (coefficients n)) radius (powℝ radius n)
      ∙ cong (_· powℝ radius n) (mulComm (normℂ (coefficients n)) radius)
      ∙ sym (mulAssoc radius (normℂ (coefficients n)) (powℝ radius n)))
    (mulPres≤R-0≤ (normℂ (formalPrimitiveℂ constant coefficients (suc n))) (normℂ (coefficients n))
      (powℝ radius (suc n)) (powNonnegative radius (suc n) nonnegative)
      (formalPrimitiveℂCoefficientBound constant coefficients n))
