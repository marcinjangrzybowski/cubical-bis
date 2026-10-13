module Cubical.Analysis.Complex.Calculus.Derivative.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties
open import Cubical.Analysis.Real.Calculus.Derivative.Uniqueness using (derivativeValueUniqueAt)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Restriction

opaque
  complexDerivativeValueUniqueAt : ∀ f z a b →
    IsComplexDerivativeAt f a z → IsComplexDerivativeAt f b z → a ≡ b
  complexDerivativeValueUniqueAt f z a b first second = ℂ≡
    (derivativeValueUniqueAt (re ∘ f ∘ horizontalComplexLine z) (re z) (re a) (re b)
      (complexDerivativeHorizontalRealAt f a z first) (complexDerivativeHorizontalRealAt f b z second))
    (derivativeValueUniqueAt (im ∘ f ∘ horizontalComplexLine z) (re z) (im a) (im b)
      (complexDerivativeHorizontalImaginaryAt f a z first) (complexDerivativeHorizontalImaginaryAt f b z second))

  complexDerivativeFunctionUnique : ∀ f d e →
    IsComplexDerivative f d → IsComplexDerivative f e → d ≡ e
  complexDerivativeFunctionUnique f d e first second =
    funExt λ z → complexDerivativeValueUniqueAt f z (d z) (e z) (first z) (second z)

HasComplexDerivativeAt : (ℂ → ℂ) → ℂ → Type₀
HasComplexDerivativeAt f z = Σ[ d ∈ ℂ ] IsComplexDerivativeAt f d z

isPropHasComplexDerivativeAt : ∀ f z → isProp (HasComplexDerivativeAt f z)
isPropHasComplexDerivativeAt f z (a , first) (b , second) = ΣPathPProp
  (λ d → isPropIsComplexDerivativeAlongAt (ℂPremetricSpace .snd) (idfun ℂ) f d z)
  (complexDerivativeValueUniqueAt f z a b first second)

HasComplexDerivative : (ℂ → ℂ) → Type₀
HasComplexDerivative f = Σ[ d ∈ (ℂ → ℂ) ] IsComplexDerivative f d

isPropHasComplexDerivative : ∀ f → isProp (HasComplexDerivative f)
isPropHasComplexDerivative f (d , first) (e , second) = ΣPathPProp
  (isPropIsComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ) f)
  (complexDerivativeFunctionUnique f d e first second)
