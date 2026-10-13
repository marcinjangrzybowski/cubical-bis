module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Primitive.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Domain
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Translation
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem.Along

-- Construct both values along a path in a centered closed convergence ball.
-- The interval retraction supplies total real-parameter functions without
-- extending the series to arbitrary complex points outside its domain.
module _ {a b : ℝ} (path : UniformComplexPath a b) (center : ℂ)
  (coefficients : ComplexSequence) (radius : ℝ)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) where
  private module P = UniformComplexPath path

  centeredPowerSeriesPathPoint : ClosedInterval a b → ClosedComplexNormRadius radius
  centeredPowerSeriesPathPoint (t , lo , hi) = P.curve t -ℂ center , bounded t lo hi

  private
    -- Keep the completed-real clamp behind its section equation: consumers
    -- need that equation, not normalization of the retraction itself.
    opaque
      point : ℝ → ClosedComplexNormRadius radius
      point = centeredPowerSeriesPathPoint ∘ fst (clampIntervalRetractionNE a b P.ordered)
      point-on : ∀ (x : ClosedInterval a b) → point (fst x) ≡ centeredPowerSeriesPathPoint x
      point-on x = Σ≡Prop (λ z → isProp≤ℝ (normℂ z) radius)
        (cong (λ t → P.curve t -ℂ center)
          (clampIntervalFix a b (fst x) (fst (snd x)) (snd (snd x))))

    pointUniform : IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      centeredPowerSeriesPathPoint (ClosedComplexNormRadiusPremetricSpace radius .snd)
    pointUniform ε = PT.map (λ { (δ , near) → δ , λ x y close →
      addℂ-presClosenessR (-ℂ center) (P.curve (fst x)) (P.curve (fst y)) ε (near x y close) })
      (pathIsRadiuswiseUniformlyContinuous path ε)

  powerSeriesPathValue : ℝ → ℂ
  powerSeriesPathValue = closedComplexPowerSeriesValue coefficients radius witness ∘ point

  powerSeriesPathValue-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) →
    powerSeriesPathValue t ≡ closedComplexPowerSeriesValue coefficients radius witness (centeredPowerSeriesPathPoint (t , lo , hi))
  powerSeriesPathValue-on t lo hi = cong (closedComplexPowerSeriesValue coefficients radius witness) (point-on (t , lo , hi))

  powerSeriesPathHasSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)) (powerSeriesPathValue t)
  powerSeriesPathHasSum t lo hi = subst (HasComplexSum (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)))
    (sym (powerSeriesPathValue-on t lo hi))
    (closedComplexPowerSeriesHasSum coefficients radius witness (centeredPowerSeriesPathPoint (t , lo , hi)))

  module _ (constant : ℂ) (nonnegative : 0ℝ ≤ℝ radius) where
    private
      antiderivative : ClosedComplexNormRadius radius → ℂ
      antiderivative = closedComplexPowerSeriesPrimitive coefficients radius witness constant nonnegative

    powerSeriesPathPrimitive : ℝ → ℂ
    powerSeriesPathPrimitive = antiderivative ∘ point

    powerSeriesPathPrimitive-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) →
      powerSeriesPathPrimitive t ≡ antiderivative (centeredPowerSeriesPathPoint (t , lo , hi))
    powerSeriesPathPrimitive-on t lo hi = cong antiderivative (point-on (t , lo , hi))

    powerSeriesPathPrimitiveHasSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
      HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (P.curve t -ℂ center)) (powerSeriesPathPrimitive t)
    powerSeriesPathPrimitiveHasSum t lo hi = subst
      (HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (P.curve t -ℂ center)))
      (sym (powerSeriesPathPrimitive-on t lo hi))
      (closedComplexPowerSeriesPrimitiveHasSum coefficients radius witness constant nonnegative (centeredPowerSeriesPathPoint (t , lo , hi)))

    opaque
      powerSeriesPathHasUniformPrimitive : IsUniformPrimitiveValuesAlongPath powerSeriesPathPrimitive powerSeriesPathValue path
      powerSeriesPathHasUniformPrimitive = subst2
        (IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst))
        (sym (funExt λ (t , lo , hi) → powerSeriesPathPrimitive-on t lo hi))
        (sym (funExt λ (t , lo , hi) → powerSeriesPathValue-on t lo hi))
        (unshiftUniformComplexDerivativeCoordinate (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst)
          (antiderivative ∘ centeredPowerSeriesPathPoint)
          (closedComplexPowerSeriesValue coefficients radius witness ∘ centeredPowerSeriesPathPoint) center
          (uniformComplexDerivativeAlongPrecompose (ClosedIntervalPremetricSpace a b .snd)
            (ClosedComplexNormRadiusPremetricSpace radius .snd) centeredPowerSeriesPathPoint fst antiderivative
            (closedComplexPowerSeriesValue coefficients radius witness) pointUniform
            (closedComplexPowerSeriesPrimitiveHasUniformDerivative coefficients radius witness constant nonnegative)))

    private
      endpointEquality : pathFinish path ≡ pathStart path →
        centeredPowerSeriesPathPoint (b , P.ordered , ≤ℝ-refl b) ≡
        centeredPowerSeriesPathPoint (a , ≤ℝ-refl a , P.ordered)
      endpointEquality closed = Σ≡Prop (λ z → isProp≤ℝ (normℂ z) radius) (cong (_-ℂ center) closed)

    powerSeriesPathPrimitiveEndpointsAgree : pathFinish path ≡ pathStart path →
      powerSeriesPathPrimitive b ≡ powerSeriesPathPrimitive a
    powerSeriesPathPrimitiveEndpointsAgree closed = powerSeriesPathPrimitive-on b P.ordered (≤ℝ-refl b)
      ∙ cong antiderivative (endpointEquality closed)
      ∙ sym (powerSeriesPathPrimitive-on a (≤ℝ-refl a) P.ordered)
