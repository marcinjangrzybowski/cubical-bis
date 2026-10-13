module Cubical.Analysis.Complex.Integration.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add as Real
import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub as Real
import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg as Real
import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Scale as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Integration.Base

addHasComplexRiemannIntegral : ∀ {a b} f g value other →
  HasComplexRiemannIntegralOn f a b value → HasComplexRiemannIntegralOn g a b other →
  HasComplexRiemannIntegralOn (λ t → f t +ℂ g t) a b (value +ℂ other)
addHasComplexRiemannIntegral f g value other first second =
  Real.addHasRiemannIntegral (re ∘ f) (re ∘ g) (re value) (re other) (fst first) (fst second) ,
  Real.addHasRiemannIntegral (im ∘ f) (im ∘ g) (im value) (im other) (snd first) (snd second)

negHasComplexRiemannIntegral : ∀ {a b} f value → HasComplexRiemannIntegralOn f a b value →
  HasComplexRiemannIntegralOn (λ t → -ℂ f t) a b (-ℂ value)
negHasComplexRiemannIntegral f value integral =
  Real.negHasRiemannIntegral (re ∘ f) (re value) (fst integral) ,
  Real.negHasRiemannIntegral (im ∘ f) (im value) (snd integral)

subHasComplexRiemannIntegral : ∀ {a b} f g value other →
  HasComplexRiemannIntegralOn f a b value → HasComplexRiemannIntegralOn g a b other →
  HasComplexRiemannIntegralOn (λ t → f t -ℂ g t) a b (value -ℂ other)
subHasComplexRiemannIntegral f g value other first second =
  addHasComplexRiemannIntegral f (λ t → -ℂ g t) value (-ℂ other) first (negHasComplexRiemannIntegral g other second)

opaque
  scaleHasComplexRiemannIntegral : ∀ {a b} c f value → HasComplexRiemannIntegralOn f a b value →
    HasComplexRiemannIntegralOn (λ t → c ·ℂ f t) a b (c ·ℂ value)
  scaleHasComplexRiemannIntegral c f value integral =
    Real.subHasRiemannIntegral (λ t → re c · re (f t)) (λ t → im c · im (f t)) (re c · re value) (im c · im value)
      (Real.scaleHasRiemannIntegral (re c) (re ∘ f) (re value) (fst integral))
      (Real.scaleHasRiemannIntegral (im c) (im ∘ f) (im value) (snd integral)) ,
    Real.addHasRiemannIntegral (λ t → re c · im (f t)) (λ t → im c · re (f t)) (re c · im value) (im c · re value)
      (Real.scaleHasRiemannIntegral (re c) (im ∘ f) (im value) (snd integral))
      (Real.scaleHasRiemannIntegral (im c) (re ∘ f) (re value) (fst integral))

conjugateHasComplexRiemannIntegral : ∀ {a b} f value → HasComplexRiemannIntegralOn f a b value →
  HasComplexRiemannIntegralOn (conjugate ∘ f) a b (conjugate value)
conjugateHasComplexRiemannIntegral f value integral = fst integral , Real.negHasRiemannIntegral (im ∘ f) (im value) (snd integral)
