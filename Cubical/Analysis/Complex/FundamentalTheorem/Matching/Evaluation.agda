module Cubical.Analysis.Complex.FundamentalTheorem.Matching.Evaluation where

-- Uniform bounds for simultaneous perturbation of coefficients and the
-- evaluation point. Synthetic division consists of finitely many such
-- evaluations, so the same estimates also control deflation.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (zero; suc)
open import Cubical.Data.Vec using ([]; _∷_; lookup)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Norm.Difference
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.EvaluationStep
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition
import Cubical.Analysis.Complex.Polynomial.Monic.DeflationAlgebra as DeflationDefinition

private module R = IdentitiesDefinition.Identities ℝCommRing
private module D = DeflationDefinition.Deflation ℂCommRing

monicEvaluationBound : ℕ → ℚ₊ → ℚ₊ → ℚ₊
monicEvaluationBound zero A B = 1
monicEvaluationBound (suc n) A B = A +₊ (B ·₊ monicEvaluationBound n A B)

monicEvaluationLipschitz : ℕ → ℚ₊ → ℚ₊ → ℚ₊
monicEvaluationLipschitz zero A B = 1
monicEvaluationLipschitz (suc n) A B =
  1 +₊ (monicEvaluationBound n A B +₊ (B ·₊ monicEvaluationLipschitz n A B))

monicQuotientLipschitz : ℕ → ℚ₊ → ℚ₊ → ℚ₊
monicQuotientLipschitz zero A B = 1
monicQuotientLipschitz (suc n) A B = monicEvaluationLipschitz (suc n) A B +₊ monicQuotientLipschitz n A B

opaque
  monicEvaluation-bound : ∀ {n} (p : MonicPolynomial n) z A B →
    CoefficientNormBound p ⟦ A ⟧₊ → normℂ z ≤ℝ ⟦ B ⟧₊ →
    normℂ (evaluateMonic p z) ≤ℝ ⟦ monicEvaluationBound n A B ⟧₊
  monicEvaluation-bound [] z A B pb zb =
    subst {x = 1ℝ} {y = normℂ 1ℂ} (_≤ℝ 1ℝ) (sym normℂ-one) (≤ℝ-refl 1ℝ)
  monicEvaluation-bound {n = suc n} (a ∷ p) z A B pb zb =
    subst {x = a +ℂ z ·ℂ evaluateMonic p z} {y = evaluateMonic (a ∷ p) z}
      (λ v → normℂ v ≤ℝ ⟦ monicEvaluationBound (suc n) A B ⟧₊)
      (sym (D.evaluate-cons a p z))
      (rationalHornerBound a z (evaluateMonic p z) A B (monicEvaluationBound n A B)
        (pb zero) zb (monicEvaluation-bound {n = n} p z A B (λ i → pb (suc i)) zb))

  monicEvaluation-difference : ∀ {n} (p q : MonicPolynomial n) r s A B δ →
    0ℝ ≤ℝ δ → CoefficientNormBound p ⟦ A ⟧₊ →
    normℂ r ≤ℝ ⟦ B ⟧₊ → normℂ s ≤ℝ ⟦ B ⟧₊ →
    CoefficientDifferenceBound p q δ → normℂ (r -ℂ s) ≤ℝ δ →
    normℂ (evaluateMonic p r -ℂ evaluateMonic q s) ≤ℝ ⟦ monicEvaluationLipschitz n A B ⟧₊ · δ
  monicEvaluation-difference [] [] r s A B δ nonnegative pb rb sb pq rs =
    subst2 _≤ℝ_ (sym (cong normℂ (+ℂInvR 1ℂ) ∙ normℂ-zero)) (sym (mulIdL δ)) nonnegative
  monicEvaluation-difference {n = suc n} (a ∷ p) (b ∷ q) r s A B δ nonnegative pb rb sb pq rs =
    subst (λ v → normℂ v ≤ℝ ⟦ monicEvaluationLipschitz (suc n) A B ⟧₊ · δ)
      (sym (cong₂ _-ℂ_ (D.evaluate-cons a p r) (D.evaluate-cons b q s)))
      (rationalHornerDifference a b r s (evaluateMonic p r) (evaluateMonic q s)
        (monicEvaluationBound n A B) B (monicEvaluationLipschitz n A B) δ
        (monicEvaluation-bound p r A B (λ i → pb (suc i)) rb) sb (pq zero) rs
        (monicEvaluation-difference p q r s A B δ nonnegative (λ i → pb (suc i)) rb sb
          (λ i → pq (suc i)) rs))

  monicQuotient-difference : ∀ {n} (p q : MonicPolynomial (suc n)) r s A B δ →
    0ℝ ≤ℝ δ → CoefficientNormBound p ⟦ A ⟧₊ →
    normℂ r ≤ℝ ⟦ B ⟧₊ → normℂ s ≤ℝ ⟦ B ⟧₊ →
    CoefficientDifferenceBound p q δ → normℂ (r -ℂ s) ≤ℝ δ →
    CoefficientDifferenceBound (quotientMonic p r) (quotientMonic q s) (⟦ monicQuotientLipschitz n A B ⟧₊ · δ)
  monicQuotient-difference (a ∷ []) (b ∷ []) r s A B δ nonnegative pb rb sb pq rs ()
  monicQuotient-difference {n = suc n} (a ∷ b ∷ p) (c ∷ d ∷ q) r s A B δ nonnegative pb rb sb pq rs zero =
    subst (λ v → normℂ v ≤ℝ ⟦ monicQuotientLipschitz (suc n) A B ⟧₊ · δ)
      (sym (cong₂ _-ℂ_
        (cong (lookup zero) (D.quotient-cons a (b ∷ p) r))
        (cong (lookup zero) (D.quotient-cons c (d ∷ q) s))))
      (≤ℝ-trans (normℂ (evaluateMonic (b ∷ p) r -ℂ evaluateMonic (d ∷ q) s))
        (⟦ monicEvaluationLipschitz (suc n) A B ⟧₊ · δ) (⟦ monicQuotientLipschitz (suc n) A B ⟧₊ · δ)
        (monicEvaluation-difference (b ∷ p) (d ∷ q) r s A B δ nonnegative
          (λ i → pb (suc i)) rb sb (λ i → pq (suc i)) rs)
        (mulPres≤R-0≤ ⟦ monicEvaluationLipschitz (suc n) A B ⟧₊
          ⟦ monicQuotientLipschitz (suc n) A B ⟧₊ δ nonnegative
          (radius-sumL (monicEvaluationLipschitz (suc n) A B) (monicQuotientLipschitz n A B))))
  monicQuotient-difference {n = suc n} (a ∷ b ∷ p) (c ∷ d ∷ q) r s A B δ nonnegative pb rb sb pq rs (suc i) =
    subst (λ v → normℂ v ≤ℝ ⟦ monicQuotientLipschitz (suc n) A B ⟧₊ · δ)
      (sym (cong₂ _-ℂ_
        (cong (lookup (suc i)) (D.quotient-cons a (b ∷ p) r))
        (cong (lookup (suc i)) (D.quotient-cons c (d ∷ q) s))))
      (coefficientDifference-monotone (quotientMonic (b ∷ p) r) (quotientMonic (d ∷ q) s)
        (⟦ monicQuotientLipschitz n A B ⟧₊ · δ) (⟦ monicQuotientLipschitz (suc n) A B ⟧₊ · δ)
        (mulPres≤R-0≤ ⟦ monicQuotientLipschitz n A B ⟧₊
          ⟦ monicQuotientLipschitz (suc n) A B ⟧₊ δ nonnegative
          (radius-sumR (monicEvaluationLipschitz (suc n) A B) (monicQuotientLipschitz n A B)))
        (monicQuotient-difference (b ∷ p) (d ∷ q) r s A B δ nonnegative
          (λ j → pb (suc j)) rb sb (λ j → pq (suc j)) rs) i)
