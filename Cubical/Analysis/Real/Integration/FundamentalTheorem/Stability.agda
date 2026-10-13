module Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import Cubical.Data.Nat.Order as ℕ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Sequence.Uniform
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First

open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability.Estimates
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability.Remainder

opaque
  uniformLimitOfIntegralIncrementsHasUniformDerivative : ∀ (F f : ℝ → ℝ)
    (functions derivatives : ℕ → ℝ → ℝ) a b →
    HasIntegralIncrementsOn F f a b →
    (∀ n → IsRadiuswiseUniformDerivativeOn (functions n) (derivatives n) a b) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (λ x → f (fst x)) →
    IsRadiuswiseUniformDerivativeOn F f a b
  uniformLimitOfIntegralIncrementsHasUniformDerivative F f functions derivatives a b increments derivative uniform ε =
    PT.rec squash₁ fromTail (uniform (ε /4₊))
    where
    radiusPath : (rat (fst (ε /4₊)) + rat (fst (ε /4₊))) + rat (fst (ε /2₊)) ≡ rat (fst ε)
    radiusPath = cong (_+ rat (fst (ε /2₊)))
      (rat+rat (fst (ε /4₊)) (fst (ε /4₊)) ∙ cong rat (1/2∈ℚ./4+/4≡/2 (fst ε)))
      ∙ rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε))
    slopeBound : ∀ N →
      (∀ n → N ℕ.≤ n → ∀ (x : ClosedInterval a b) → derivatives n (fst x) ∼[ ε /4₊ ] f (fst x)) →
      ∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z - derivatives N z) ≤ℝ rat (fst (ε /4₊))
    slopeBound N near z lower upper =
      subst (_≤ℝ rat (fst (ε /4₊))) (absSubComm (derivatives N z) (f z))
        (<ℝ-weaken (absℝ (derivatives N z - f z)) (rat (fst (ε /4₊)))
          (closeness→absDifference< (derivatives N z) (f z) (ε /4₊) (near N ℕ.≤-refl (z , lower , upper))))

    fromTail : Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → ∀ (x : ClosedInterval a b) → derivatives n (fst x) ∼[ ε /4₊ ] f (fst x)) →
      ∃[ δ ∈ ℚ₊ ] (∀ x y → a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b → x ∼[ δ ] y →
        absℝ ((F y - F x) - f x · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x))
    fromTail (N , near) = PT.map atRadius (derivative N (ε /2₊))
      where
      atRadius : Σ[ δ ∈ ℚ₊ ] (∀ x y → a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b → x ∼[ δ ] y →
        absℝ ((functions N y - functions N x) - derivatives N x · (y - x)) ≤ℝ rat (fst (ε /2₊)) · absℝ (y - x)) →
        Σ[ δ ∈ ℚ₊ ] (∀ x y → a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b → x ∼[ δ ] y →
          absℝ ((F y - F x) - f x · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x))
      atRadius (δ , approximate) = δ , λ x y a≤x x≤b a≤y y≤b close →
        subst (absℝ ((F y - F x) - f x · (y - x)) ≤ℝ_)
          (cong (_· absℝ (y - x)) radiusPath)
          (uniformDerivativeRemainderTransferBound (F y - F x) (functions N y - functions N x)
            (f x) (derivatives N x) (y - x) (rat (fst (ε /4₊))) (rat (fst (ε /2₊)))
            (integralIncrementsDifferenceBound F (functions N) f (derivatives N) a b (rat (fst (ε /4₊)))
              increments (uniformDerivativeHasIntegralIncrements (functions N) (derivatives N) a b (derivative N))
              (λ z a≤z z≤b → slopeBound N near z a≤z z≤b) (x , a≤x , x≤b) (y , a≤y , y≤b))
            (slopeBound N near x a≤x x≤b) (approximate x y a≤x x≤b a≤y y≤b close))
