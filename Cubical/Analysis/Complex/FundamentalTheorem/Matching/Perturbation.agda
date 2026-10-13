module Cubical.Analysis.Complex.FundamentalTheorem.Matching.Perturbation where

-- Metric forms of the finite evaluation and synthetic-division estimates.
-- The rational tolerance functions precede all choices of nearby roots.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Vec using (lookup)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Evaluation

twoRadius-nonnegative : ∀ δ → 0ℝ ≤ℝ ⟦ δ ⟧₊ + ⟦ δ ⟧₊
twoRadius-nonnegative δ = subst (0ℝ ≤ℝ_) (sym (rat+rat (fst δ) (fst δ))) (radius-nonnegative (δ +₊ δ))

closeness→differenceBound : ∀ z w δ → z ∼ℂ[ δ ] w → normℂ (z -ℂ w) ≤ℝ ⟦ δ ⟧₊ + ⟦ δ ⟧₊
closeness→differenceBound z w δ close = <ℝ-weaken (normℂ (z -ℂ w)) (⟦ δ ⟧₊ + ⟦ δ ⟧₊)
  (closeness→normℂ-difference< z w δ close)

coefficientCloseness→differenceBound : ∀ {n} (p q : MonicPolynomial n) δ →
  CoefficientCloseness p δ q → CoefficientDifferenceBound p q (⟦ δ ⟧₊ + ⟦ δ ⟧₊)
coefficientCloseness→differenceBound p q δ close i = closeness→differenceBound (lookup i p) (lookup i q) δ (close i)

opaque
  monicQuotient-closeness : ∀ {n} (p q : MonicPolynomial (suc n)) r s A B ε →
    CoefficientNormBound p ⟦ A ⟧₊ → normℂ r ≤ℝ ⟦ B ⟧₊ → normℂ s ≤ℝ ⟦ B ⟧₊ →
    CoefficientCloseness p (scaleTolerance (monicQuotientLipschitz n A B) ε) q →
    r ∼ℂ[ scaleTolerance (monicQuotientLipschitz n A B) ε ] s →
    CoefficientCloseness (quotientMonic p r) ε (quotientMonic q s)
  monicQuotient-closeness {n} p q r s A B ε pb rb sb pq rs i =
    scaledBound→closeness (monicQuotientLipschitz n A B) ε
      (lookup i (quotientMonic p r)) (lookup i (quotientMonic q s))
      (monicQuotient-difference p q r s A B (⟦ δ ⟧₊ + ⟦ δ ⟧₊) (twoRadius-nonnegative δ)
        pb rb sb (coefficientCloseness→differenceBound p q δ pq) (closeness→differenceBound r s δ rs) i)
    where
    δ : ℚ₊
    δ = scaleTolerance (monicQuotientLipschitz n A B) ε

  monicEvaluation-nearZero : ∀ {n} (p q : MonicPolynomial n) z A B ε →
    CoefficientNormBound q ⟦ A ⟧₊ → normℂ z ≤ℝ ⟦ B ⟧₊ → evaluateMonic p z ≡ 0ℂ →
    CoefficientCloseness p (scaleTolerance (monicEvaluationLipschitz n A B) ε) q →
    modulusℂ (evaluateMonic q z) <ℝ ⟦ ε ⟧₊
  monicEvaluation-nearZero {n} p q z A B ε qb zb root close =
    ≤<ℝ-trans (modulusℂ value) (normℂ value) ⟦ ε ⟧₊ (modulusℂ≤normℂ value)
      (≤<ℝ-trans (normℂ value) ⟦ ε /2₊ ⟧₊ ⟦ ε ⟧₊ bounded
        (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
    where
    δ : ℚ₊
    δ = scaleTolerance (monicEvaluationLipschitz n A B) ε
    value : ℂ
    value = evaluateMonic q z
    difference : value -ℂ evaluateMonic p z ≡ value
    difference = cong (λ u → value -ℂ u) root ∙ cong (value +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR value

    bounded : normℂ value ≤ℝ ⟦ ε /2₊ ⟧₊
    bounded = subst2 _≤ℝ_ (cong normℂ difference) (scaleTolerance-law (monicEvaluationLipschitz n A B) ε)
      (monicEvaluation-difference q p z z A B (⟦ δ ⟧₊ + ⟦ δ ⟧₊) (twoRadius-nonnegative δ)
        qb zb zb
        (coefficientCloseness→differenceBound q p δ
          (λ i → sym∼ℂ (lookup i p) (lookup i q) δ (close i)))
        (closeness→differenceBound z z δ (refl∼ℂ z δ)))
