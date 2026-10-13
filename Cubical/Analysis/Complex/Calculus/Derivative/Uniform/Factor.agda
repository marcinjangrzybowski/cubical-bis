module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Factor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

-- A continuous divided difference avoids division by a possibly zero chord.
-- Joint radiuswise uniform continuity on the chosen domain supplies the
-- uniform derivative estimate, including along paths with repeated points.
opaque
  uniformlyContinuousComplexDifferenceFactorGivesUniformDerivative : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) (factor : A × A → ℂ) →
    (∀ x y → f y -ℂ f x ≡ factor (x , y) ·ℂ (coordinate y -ℂ coordinate x)) →
    (∀ x → factor (x , x) ≡ d x) →
    IsRadiuswiseUniformlyContinuous (PremetricProductStr source source) factor (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate f d
  uniformlyContinuousComplexDifferenceFactorGivesUniformDerivative source coordinate f d factor factorization diagonal continuous ε =
    PT.map (λ { (δ , near) → δ , λ x y close →
      subst (λ error → normℂ error ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (sym (cong (_-ℂ d x ·ℂ (coordinate y -ℂ coordinate x)) (factorization x y)
          ∙ sym (ℂRing.·DistL- (factor (x , y)) (d x) (coordinate y -ℂ coordinate x))))
        (normℂ-mulBound (factor (x , y) -ℂ d x) (coordinate y -ℂ coordinate x)
          (rat (fst ε)) (normℂ (coordinate y -ℂ coordinate x))
          (subst (λ value → normℂ (factor (x , y) -ℂ value) ≤ℝ rat (fst ε)) (diagonal x)
            (<ℝ-weaken (normℂ (factor (x , y) -ℂ factor (x , x))) (rat (fst ε))
              (halfNormCloseness (factor (x , y)) (factor (x , x)) ε
                (sym∼ℂ (factor (x , x)) (factor (x , y)) (ε /2₊)
                  (near (x , x) (x , y) (PremetricStr.isRefl≈ source x δ , close))))))
          (≤ℝ-refl (normℂ (coordinate y -ℂ coordinate x)))) }) (continuous (ε /2₊))
