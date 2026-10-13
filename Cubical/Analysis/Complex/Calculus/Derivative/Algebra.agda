module Cubical.Analysis.Complex.Calculus.Derivative.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError
import Cubical.Analysis.Complex.Calculus.Derivative.Identities as Identities

private module E = Identities.RemainderAlgebra ℂCommRing

module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) (coordinate : A → ℂ) where
  addHasComplexDerivativeAlongAt : ∀ f g d e x →
    IsComplexDerivativeAlongAt source coordinate f d x → IsComplexDerivativeAlongAt source coordinate g e x →
    IsComplexDerivativeAlongAt source coordinate (λ y → f y +ℂ g y) (d +ℂ e) x
  addHasComplexDerivativeAlongAt f g d e x first second =
    smallComplexErrorCong source x (λ y → coordinate y -ℂ coordinate x)
      (λ y → complexDerivativeErrorAlong coordinate f d x y +ℂ complexDerivativeErrorAlong coordinate g e x y)
      (complexDerivativeErrorAlong coordinate (λ y → f y +ℂ g y) (d +ℂ e) x)
      (λ y → sym (E.add-error (f x) (f y) (g x) (g y) d e (coordinate y -ℂ coordinate x)))
      (smallComplexErrorAdd source x (λ y → coordinate y -ℂ coordinate x)
        (complexDerivativeErrorAlong coordinate f d x) (complexDerivativeErrorAlong coordinate g e x) first second)

  negHasComplexDerivativeAlongAt : ∀ f d x → IsComplexDerivativeAlongAt source coordinate f d x →
    IsComplexDerivativeAlongAt source coordinate (λ y → -ℂ f y) (-ℂ d) x
  negHasComplexDerivativeAlongAt f d x differentiable =
    smallComplexErrorCong source x (λ y → coordinate y -ℂ coordinate x)
      (λ y → -ℂ complexDerivativeErrorAlong coordinate f d x y)
      (complexDerivativeErrorAlong coordinate (λ y → -ℂ f y) (-ℂ d) x)
      (λ y → sym (E.neg-error (f x) (f y) d (coordinate y -ℂ coordinate x)))
      (smallComplexErrorNeg source x (λ y → coordinate y -ℂ coordinate x)
        (complexDerivativeErrorAlong coordinate f d x) differentiable)

  addHasComplexDerivativeAlong : ∀ f g d e →
    IsComplexDerivativeAlong source coordinate f d → IsComplexDerivativeAlong source coordinate g e →
    IsComplexDerivativeAlong source coordinate (λ y → f y +ℂ g y) (λ y → d y +ℂ e y)
  addHasComplexDerivativeAlong f g d e first second x =
    addHasComplexDerivativeAlongAt f g (d x) (e x) x (first x) (second x)

  negHasComplexDerivativeAlong : ∀ f d → IsComplexDerivativeAlong source coordinate f d →
    IsComplexDerivativeAlong source coordinate (λ y → -ℂ f y) (λ y → -ℂ d y)
  negHasComplexDerivativeAlong f d differentiable x = negHasComplexDerivativeAlongAt f (d x) x (differentiable x)

  subHasComplexDerivativeAlong : ∀ f g d e →
    IsComplexDerivativeAlong source coordinate f d → IsComplexDerivativeAlong source coordinate g e →
    IsComplexDerivativeAlong source coordinate (λ y → f y -ℂ g y) (λ y → d y -ℂ e y)
  subHasComplexDerivativeAlong f g d e first second =
    addHasComplexDerivativeAlong f (λ y → -ℂ g y) d (λ y → -ℂ e y) first
      (negHasComplexDerivativeAlong g e second)

addHasComplexDerivative : ∀ f g d e → IsComplexDerivative f d → IsComplexDerivative g e →
  IsComplexDerivative (λ z → f z +ℂ g z) (λ z → d z +ℂ e z)
addHasComplexDerivative = addHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)

negHasComplexDerivative : ∀ f d → IsComplexDerivative f d →
  IsComplexDerivative (λ z → -ℂ f z) (λ z → -ℂ d z)
negHasComplexDerivative = negHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)

subHasComplexDerivative : ∀ f g d e → IsComplexDerivative f d → IsComplexDerivative g e →
  IsComplexDerivative (λ z → f z -ℂ g z) (λ z → d z -ℂ e z)
subHasComplexDerivative = subHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)
