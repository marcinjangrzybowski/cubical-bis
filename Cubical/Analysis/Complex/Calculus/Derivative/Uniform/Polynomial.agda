module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_; mul-rat)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤; mulPres≤R-0≤)
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Polynomial.Differential.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates using (halfNormCloseness)
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

private module M = PremetricStr (ℂPremetricSpace .snd)

opaque
  -- Reuse the polynomial Newton remainder estimate, whose constant is
  -- uniform on a norm ball. No new polynomial induction is needed.
  polynomialHasUniformComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℂ) p radius →
    (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate
      (evaluatePolynomialℂ p ∘ coordinate) (polynomialDerivativeℂ p ∘ coordinate)
  polynomialHasUniformComplexDerivativeAlong {A = A} source coordinate p radius bounded continuous ε = do
    (n , variationBound) ← ∃naturalUpperBound (polynomialDerivativeVariationℂ p radius)
    (δ , near) ← continuous ((ε ₊／₊ naturalBound n) /2₊)
    return (δ , λ x y close → estimate (coordinate x) (coordinate y) (bounded x) (bounded y)
      (naturalBound n) (<ℝ-weaken (polynomialDerivativeVariationℂ p radius) (rat (naturalRational n)) variationBound)
      (<ℝ-weaken (normℂ (coordinate y -ℂ coordinate x)) (rat (fst (ε ₊／₊ naturalBound n)))
        (halfNormCloseness (coordinate y) (coordinate x) (ε ₊／₊ naturalBound n)
          (M.isSym≈ (coordinate x) (coordinate y) ((ε ₊／₊ naturalBound n) /2₊) (near x y close)))))
    where
    estimate : ∀ z w → normℂ z ≤ℝ radius → normℂ w ≤ℝ radius → ∀ B →
      polynomialDerivativeVariationℂ p radius ≤ℝ rat (fst B) →
      normℂ (w -ℂ z) ≤ℝ rat (fst (ε ₊／₊ B)) →
      normℂ ((evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p z) -ℂ polynomialDerivativeℂ p z ·ℂ (w -ℂ z)) ≤ℝ
        rat (fst ε) · normℂ (w -ℂ z)
    estimate z w zb wb B variation small = ≤ℝ-trans
      (normℂ ((evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p z) -ℂ polynomialDerivativeℂ p z ·ℂ (w -ℂ z)))
      ((polynomialDerivativeVariationℂ p radius · normℂ (w -ℂ z)) · normℂ (w -ℂ z))
      (rat (fst ε) · normℂ (w -ℂ z))
      (polynomialNewtonRemainder-boundℂ p radius (normℂ (w -ℂ z)) z w z zb wb zb
        (≤ℝ-refl (normℂ (w -ℂ z)))
        (subst (_≤ℝ normℂ (w -ℂ z)) (sym (cong normℂ (+ℂInvR z) ∙ normℂ-zero)) (normℂ-nonnegative (w -ℂ z))))
      (mulPres≤R-0≤ (polynomialDerivativeVariationℂ p radius · normℂ (w -ℂ z)) (rat (fst ε))
        (normℂ (w -ℂ z)) (normℂ-nonnegative (w -ℂ z))
        (subst (polynomialDerivativeVariationℂ p radius · normℂ (w -ℂ z) ≤ℝ_)
          (mul-rat (fst B) (fst (ε ₊／₊ B)) ∙ cong rat (·／ B ε))
          (mulPres≤ (polynomialDerivativeVariationℂ p radius) (rat (fst B))
            (normℂ (w -ℂ z)) (rat (fst (ε ₊／₊ B)))
            (<ℝ-weaken 0ℝ (rat (fst B)) (positiveSlack B)) (normℂ-nonnegative (w -ℂ z)) variation small)))
