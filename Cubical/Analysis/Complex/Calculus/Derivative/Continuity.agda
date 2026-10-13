module Cubical.Analysis.Complex.Calculus.Derivative.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
import Cubical.Analysis.Complex.Calculus.Derivative.Identities as Identities

private module E = Identities.RemainderAlgebra ℂCommRing

opaque
  complexDerivativeLocalLinearBoundAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f : A → ℂ) d x →
    IsComplexDerivativeAlongAt source coordinate f d x → ∀ B → normℂ d ≤ℝ rat (fst B) →
    ∃[ δ ∈ ℚ₊ ] (∀ y → PremetricStr._≈[_]_ source x δ y →
      normℂ (f y -ℂ f x) ≤ℝ rat (fst (1₊ +₊ B)) · normℂ (coordinate y -ℂ coordinate x))
  complexDerivativeLocalLinearBoundAt source coordinate f d x differentiable B bounded = do
    (δ , near) ← differentiable 1₊
    return (δ , λ y close →
      subst2 _≤ℝ_ (cong normℂ (E.reconstruct (f x) (f y) d (coordinate y -ℂ coordinate x)))
        (sym (mulDistL (rat 1) (rat (fst B)) (normℂ (coordinate y -ℂ coordinate x)))
          ∙ cong (_· normℂ (coordinate y -ℂ coordinate x)) (rat+rat 1 (fst B)))
        (normℂ-addBound (complexDerivativeErrorAlong coordinate f d x y)
          (d ·ℂ (coordinate y -ℂ coordinate x))
          (rat 1 · normℂ (coordinate y -ℂ coordinate x))
          (rat (fst B) · normℂ (coordinate y -ℂ coordinate x)) (near y close)
          (normℂ-mulBound d (coordinate y -ℂ coordinate x)
            (rat (fst B)) (normℂ (coordinate y -ℂ coordinate x)) bounded
            (≤ℝ-refl (normℂ (coordinate y -ℂ coordinate x))))))

  complexDerivativeAlongAtIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f : A → ℂ) d x →
    IsContinuousAt source coordinate (ℂPremetricSpace .snd) x →
    IsComplexDerivativeAlongAt source coordinate f d x →
    IsContinuousAt source f (ℂPremetricSpace .snd) x
  complexDerivativeAlongAtIsContinuous source coordinate f d x coordinateContinuous differentiable
    .IsContinuousAt.pres≈ ε = do
    (B , bounded) ← complexNormRationalBound d
    (δ , linear) ← complexDerivativeLocalLinearBoundAt source coordinate f d x differentiable B bounded
    (η , near) ← continuousComplexNormDifferenceAt source coordinate x coordinateContinuous (ε ₊／₊ (1₊ +₊ B))
    return (min₊ δ η , λ y close → rationalLinearBoundGivesCloseness (f x) (f y)
      (normℂ (coordinate y -ℂ coordinate x)) (1₊ +₊ B) ε
      (linear y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) δ (min₊≤L δ η) close))
      (near y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) η (min₊≤R δ η) close)))

complexDerivativeAlongIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  IsComplexDerivativeAlong source coordinate f d → isContinuous source f (ℂPremetricSpace .snd)
complexDerivativeAlongIsContinuous source coordinate f d continuous differentiable x =
  complexDerivativeAlongAtIsContinuous source coordinate f (d x) x (continuous x) (differentiable x)

complexDerivativeAtIsContinuous : ∀ f d z → IsComplexDerivativeAt f d z →
  IsContinuousAt (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd) z
complexDerivativeAtIsContinuous f d z =
  complexDerivativeAlongAtIsContinuous (ℂPremetricSpace .snd) (idfun ℂ) f d z
    (snd (CategoryStructures.idᶜ {M = ℂPremetricSpace}) z)

complexDerivativeIsContinuous : ∀ f d → IsComplexDerivative f d →
  isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd)
complexDerivativeIsContinuous f d differentiable z = complexDerivativeAtIsContinuous f (d z) z (differentiable z)
