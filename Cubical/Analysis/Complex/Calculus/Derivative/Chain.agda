module Cubical.Analysis.Complex.Calculus.Derivative.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError
open import Cubical.Analysis.Complex.Calculus.Derivative.Continuity
import Cubical.Analysis.Complex.Calculus.Derivative.Identities as Identities

private module E = Identities.RemainderAlgebra ℂCommRing

-- The inner derivative provides the linear estimate and continuity needed
-- to pull back the outer remainder. No derivative continuity is assumed.
opaque
  chainHasComplexDerivativeAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate inner : A → ℂ) (outer : ℂ → ℂ) d e x →
    IsContinuousAt source coordinate (ℂPremetricSpace .snd) x →
    IsComplexDerivativeAlongAt source coordinate inner d x → IsComplexDerivativeAt outer e (inner x) →
    IsComplexDerivativeAlongAt source coordinate (outer ∘ inner) (e ·ℂ d) x
  chainHasComplexDerivativeAlongAt {A = A} source coordinate inner outer d e x coordinateContinuous first second =
    smallComplexErrorCong source x displacement (λ y → outerError y +ℂ e ·ℂ innerError y)
      (complexDerivativeErrorAlong coordinate (outer ∘ inner) (e ·ℂ d) x)
      (λ y → sym (E.chain-error (inner x) (inner y) (outer (inner x)) (outer (inner y)) d e (displacement y)))
      (smallComplexErrorAdd source x displacement outerError (λ y → e ·ℂ innerError y) outerSmall
        (smallComplexErrorMulConstant source x displacement e innerError first))
    where
    displacement : A → ℂ
    displacement y = coordinate y -ℂ coordinate x

    innerError outerError : A → ℂ
    innerError = complexDerivativeErrorAlong coordinate inner d x
    outerError y = complexDerivativeErrorAlong (idfun ℂ) outer e (inner x) (inner y)

    continuous : IsContinuousAt source inner (ℂPremetricSpace .snd) x
    continuous = complexDerivativeAlongAtIsContinuous source coordinate inner d x coordinateContinuous first

    outerSmall : IsSmallComplexErrorAt source x displacement outerError
    outerSmall ε = do
      (B , bounded) ← complexNormRationalBound d
      (δ , linear) ← complexDerivativeLocalLinearBoundAt source coordinate inner d x first B bounded
      (η , remainder) ← second (ε ₊／₊ (1₊ +₊ B))
      (ζ , near) ← continuous .IsContinuousAt.pres≈ η
      return (min₊ δ ζ , λ y close → complexErrorThroughLinearInput
        (complexDerivativeErrorAlong (idfun ℂ) outer e (inner x) (inner y))
        (normℂ (inner y -ℂ inner x)) (normℂ (displacement y)) (1₊ +₊ B) ε
        (remainder (inner y) (near y
          (PremetricStr.isMonotone≈≤ source x y (min₊ δ ζ) ζ (min₊≤R δ ζ) close)))
        (linear y (PremetricStr.isMonotone≈≤ source x y (min₊ δ ζ) δ (min₊≤L δ ζ) close)))

chainHasComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate inner d : A → ℂ) (outer e : ℂ → ℂ) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  IsComplexDerivativeAlong source coordinate inner d → IsComplexDerivative outer e →
  IsComplexDerivativeAlong source coordinate (outer ∘ inner) (λ x → e (inner x) ·ℂ d x)
chainHasComplexDerivativeAlong source coordinate inner d outer e continuous first second x =
  chainHasComplexDerivativeAlongAt source coordinate inner outer (d x) (e (inner x)) x
    (continuous x) (first x) (second (inner x))

chainHasComplexDerivative : ∀ inner d outer e → IsComplexDerivative inner d → IsComplexDerivative outer e →
  IsComplexDerivative (outer ∘ inner) (λ z → e (inner z) ·ℂ d z)
chainHasComplexDerivative inner d outer e =
  chainHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ) inner d outer e
    (snd (CategoryStructures.idᶜ {M = ℂPremetricSpace}))
