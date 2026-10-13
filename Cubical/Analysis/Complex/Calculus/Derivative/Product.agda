module Cubical.Analysis.Complex.Calculus.Derivative.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Continuity
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError
import Cubical.Analysis.Complex.Calculus.Derivative.Identities as Identities

private module E = Identities.RemainderAlgebra ℂCommRing

opaque
  mulHasComplexDerivativeAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f g : A → ℂ) d e x →
    IsContinuousAt source coordinate (ℂPremetricSpace .snd) x →
    IsComplexDerivativeAlongAt source coordinate f d x → IsComplexDerivativeAlongAt source coordinate g e x →
    IsComplexDerivativeAlongAt source coordinate (λ y → f y ·ℂ g y) (d ·ℂ g x +ℂ f x ·ℂ e) x
  mulHasComplexDerivativeAlongAt {A = A} source coordinate f g d e x coordinateContinuous first second =
    smallComplexErrorCong source x displacement
      (λ y → (g y ·ℂ errorF y +ℂ f x ·ℂ errorG y) +ℂ d ·ℂ cross y)
      (complexDerivativeErrorAlong coordinate (λ y → f y ·ℂ g y) (d ·ℂ g x +ℂ f x ·ℂ e) x)
      (λ y → sym (E.product-error (f x) (f y) (g x) (g y) d e (displacement y)))
      (smallComplexErrorAdd source x displacement
        (λ y → g y ·ℂ errorF y +ℂ f x ·ℂ errorG y) (λ y → d ·ℂ cross y)
        (smallComplexErrorAdd source x displacement (λ y → g y ·ℂ errorF y) (λ y → f x ·ℂ errorG y)
          (smallComplexErrorMulContinuous source x displacement g errorF continuous first)
          (smallComplexErrorMulConstant source x displacement (f x) errorG second))
        (smallComplexErrorMulConstant source x displacement d cross
          (smallComplexErrorContinuousFactor source x displacement g continuous)))
    where
    displacement : A → ℂ
    displacement y = coordinate y -ℂ coordinate x
    errorF errorG cross : A → ℂ
    errorF = complexDerivativeErrorAlong coordinate f d x
    errorG = complexDerivativeErrorAlong coordinate g e x
    cross y = (g y -ℂ g x) ·ℂ displacement y
    continuous : IsContinuousAt source g (ℂPremetricSpace .snd) x
    continuous = complexDerivativeAlongAtIsContinuous source coordinate g e x coordinateContinuous second

mulHasComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate f g d e : A → ℂ) →
  isContinuous source coordinate (ℂPremetricSpace .snd) →
  IsComplexDerivativeAlong source coordinate f d → IsComplexDerivativeAlong source coordinate g e →
  IsComplexDerivativeAlong source coordinate (λ y → f y ·ℂ g y) (λ y → d y ·ℂ g y +ℂ f y ·ℂ e y)
mulHasComplexDerivativeAlong source coordinate f g d e continuous first second x =
  mulHasComplexDerivativeAlongAt source coordinate f g (d x) (e x) x (continuous x) (first x) (second x)

mulHasComplexDerivative : ∀ f g d e → IsComplexDerivative f d → IsComplexDerivative g e →
  IsComplexDerivative (λ z → f z ·ℂ g z) (λ z → d z ·ℂ g z +ℂ f z ·ℂ e z)
mulHasComplexDerivative f g d e = mulHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ) f g d e
  (snd (CategoryStructures.idᶜ {M = ℂPremetricSpace}))
