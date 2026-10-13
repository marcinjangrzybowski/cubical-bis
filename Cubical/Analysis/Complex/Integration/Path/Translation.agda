module Cubical.Analysis.Complex.Integration.Path.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Translation
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path

-- A geometric translation preserves the certified velocity and speed bound.
translateComplexPath : ∀ {a b} → UniformComplexPath a b → ℂ → UniformComplexPath a b
translateComplexPath path offset .UniformComplexPath.ordered = UniformComplexPath.ordered path
translateComplexPath path offset .UniformComplexPath.curve t = UniformComplexPath.curve path t +ℂ offset
translateComplexPath path offset .UniformComplexPath.velocity = UniformComplexPath.velocity path
translateComplexPath {a} {b} path offset .UniformComplexPath.differentiable =
  uniformCurveDerivativeAlong→on (λ t → P.curve t +ℂ offset) P.velocity a b
    (translateUniformComplexDerivativeValues (ClosedIntervalPremetricSpace a b .snd)
      (fromℝ ∘ fst) (P.curve ∘ fst) (P.velocity ∘ fst) offset
      (uniformCurveDerivativeOn→along P.curve P.velocity a b P.differentiable))
  where
  module P = UniformComplexPath path
translateComplexPath path offset .UniformComplexPath.speedBound = UniformComplexPath.speedBound path
translateComplexPath path offset .UniformComplexPath.boundedSpeed = UniformComplexPath.boundedSpeed path

-- The subtraction form makes relative radius bounds apply definitionally.
recenterComplexPath : ∀ {a b} → UniformComplexPath a b → ℂ → UniformComplexPath a b
recenterComplexPath path center = translateComplexPath path (-ℂ center)
