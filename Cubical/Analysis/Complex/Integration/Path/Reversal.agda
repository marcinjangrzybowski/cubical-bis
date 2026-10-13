module Cubical.Analysis.Complex.Integration.Path.Reversal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Affine
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Reparameterization

private module R = Ring.RingTheory (CommRing→Ring ℝCommRing)

reflectParameter : ℝ → ℝ → ℝ → ℝ
reflectParameter a b t = (a + b) - t

opaque
  reflectParameterAtStart : ∀ a b → reflectParameter a b a ≡ b
  reflectParameterAtStart a b = cong (_- a) (addComm a b)
    ∙ sym (addAssoc b a (- a)) ∙ cong (b +_) (addInvR a) ∙ addIdR b

  reflectParameterAtFinish : ∀ a b → reflectParameter a b b ≡ a
  reflectParameterAtFinish a b = sym (addAssoc a b (- b)) ∙ cong (a +_) (addInvR b) ∙ addIdR a

  reflectParameterLower : ∀ a b t → a ≤ℝ t → t ≤ℝ b → a ≤ℝ reflectParameter a b t
  reflectParameterLower a b t lower upper = subst (_≤ℝ reflectParameter a b t) (reflectParameterAtFinish a b)
    (addPres≤L (- b) (- t) (a + b) (negPres≤ t b upper))

  reflectParameterUpper : ∀ a b t → a ≤ℝ t → t ≤ℝ b → reflectParameter a b t ≤ℝ b
  reflectParameterUpper a b t lower upper = subst (reflectParameter a b t ≤ℝ_) (reflectParameterAtStart a b)
    (addPres≤L (- t) (- a) (a + b) (negPres≤ a t lower))

reflectUniformParameterChange : ∀ a b → a ≤ℝ b → UniformParameterChange a b
reflectUniformParameterChange a b ordered .UniformParameterChange.ordered = ordered
reflectUniformParameterChange a b ordered .UniformParameterChange.curve = reflectParameter a b
reflectUniformParameterChange a b ordered .UniformParameterChange.velocity = λ _ → - 1ℝ
reflectUniformParameterChange a b ordered .UniformParameterChange.differentiable =
  uniformDerivativeAlongInterval→on (reflectParameter a b) (λ _ → - 1ℝ) a b
    (exactDifferenceGivesUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
      (reflectParameter a b ∘ fst) (λ _ → - 1ℝ)
      (λ x y → differenceOfSums (a + b) (- fst y) (a + b) (- fst x)
        ∙ cong (_+ ((- fst y) - (- fst x))) (subSelf (a + b))
        ∙ addIdL ((- fst y) - (- fst x)) ∙ differenceOfNegatives (fst y) (fst x)
        ∙ R.-IsMult-1 (fst y - fst x)))
reflectUniformParameterChange a b ordered .UniformParameterChange.speedBound = 1₊
reflectUniformParameterChange a b ordered .UniformParameterChange.boundedSpeed t lower upper =
  subst (_≤ℝ 1ℝ) (sym (absNeg 1ℝ ∙ absOne)) (≤ℝ-refl 1ℝ)

-- Reverse the actual curve on the same ordered interval. This also works
-- for degenerate intervals; no division by b-a is required.
reverseComplexPath : ∀ {a b} → UniformComplexPath a b → UniformComplexPath a b
reverseComplexPath {a} {b} path = reparameterizeComplexPath path
  (reflectUniformParameterChange a b (UniformComplexPath.ordered path))
  (reflectParameterLower a b) (reflectParameterUpper a b)

reverseComplexPathStartsAtFinish : ∀ {a b} (path : UniformComplexPath a b) → pathStart (reverseComplexPath path) ≡ pathFinish path
reverseComplexPathStartsAtFinish {a} {b} path = cong (UniformComplexPath.curve path) (reflectParameterAtStart a b)

reverseComplexPathFinishesAtStart : ∀ {a b} (path : UniformComplexPath a b) → pathFinish (reverseComplexPath path) ≡ pathStart path
reverseComplexPathFinishesAtStart {a} {b} path = cong (UniformComplexPath.curve path) (reflectParameterAtFinish a b)
