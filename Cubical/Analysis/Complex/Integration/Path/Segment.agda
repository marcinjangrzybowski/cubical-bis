module Cubical.Analysis.Complex.Integration.Path.Segment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Nonnegative using (oneIsNonnegative)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (isNonnegative→0≤)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Basic
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path

complexSegment : ℂ → ℂ → ℝ → ℂ
complexSegment start finish t = start +ℂ (finish -ℂ start) ·ℂ fromℝ t

segmentUniformComplexPath : ∀ start finish (B : ℚ₊) → normℂ (finish -ℂ start) ≤ℝ rat (fst B) →
  UniformComplexPath 0ℝ 1ℝ
segmentUniformComplexPath start finish B bounded .UniformComplexPath.ordered = isNonnegative→0≤ 1ℝ oneIsNonnegative
segmentUniformComplexPath start finish B bounded .UniformComplexPath.curve = complexSegment start finish
segmentUniformComplexPath start finish B bounded .UniformComplexPath.velocity = λ _ → finish -ℂ start
segmentUniformComplexPath start finish B bounded .UniformComplexPath.differentiable =
  uniformCurveDerivativeAlong→on (complexSegment start finish) (λ _ → finish -ℂ start) 0ℝ 1ℝ
    (affineHasUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace 0ℝ 1ℝ .snd) (fromℝ ∘ fst) start (finish -ℂ start))
segmentUniformComplexPath start finish B bounded .UniformComplexPath.speedBound = B
segmentUniformComplexPath start finish B bounded .UniformComplexPath.boundedSpeed t lower upper = bounded

segmentStartsAt : ∀ start finish B bounded → pathStart (segmentUniformComplexPath start finish B bounded) ≡ start
segmentStartsAt start finish B bounded = cong (start +ℂ_) (ℂRing.0RightAnnihilates (finish -ℂ start)) ∙ +ℂIdR start

segmentFinishesAt : ∀ start finish B bounded → pathFinish (segmentUniformComplexPath start finish B bounded) ≡ finish
segmentFinishesAt start finish B bounded = cong (start +ℂ_) (·ℂIdR (finish -ℂ start))
  ∙ +ℂComm start (finish -ℂ start) ∙ ℂRing.minusPlus finish start
