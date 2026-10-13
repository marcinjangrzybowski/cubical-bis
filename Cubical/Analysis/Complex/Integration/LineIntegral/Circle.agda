module Cubical.Analysis.Complex.Integration.LineIntegral.Circle where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊; _+₊_)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (subZero)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken; <ℝ-irrefl)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Properties
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.Path.Vertical
open import Cubical.Analysis.Complex.Integration.Path.Exponential
open import Cubical.Analysis.Complex.Integration.LineIntegral.Along
open import Cubical.Analysis.Complex.Integration.LineIntegral.Logarithm

private
  ordered : 0ℝ ≤ℝ twoPiℝ
  ordered = <ℝ-weaken 0ℝ twoPiℝ twoPiℝ-positive

unitCircleLogarithmicLift : ℝ → ℂ
unitCircleLogarithmicLift t = 0ℝ , t

opaque
  imaginaryExponentialHasUnitModulus : ∀ t → modulusℂ (expℂ (unitCircleLogarithmicLift t)) ≡ 1ℝ
  imaginaryExponentialHasUnitModulus t = cong modulusℂ (expℂ-imaginary t) ∙ modulusℂ-cisℝ t

  private
    circleExponentialBound : ∀ t → 0ℝ ≤ℝ t → t ≤ℝ twoPiℝ → normℂ (expℂ (unitCircleLogarithmicLift t)) ≤ℝ rat (fst (1₊ +₊ 1₊))
    circleExponentialBound t lo hi = subst (normℂ (expℂ (unitCircleLogarithmicLift t)) ≤ℝ_)
      (cong₂ _+_ (imaginaryExponentialHasUnitModulus t) (imaginaryExponentialHasUnitModulus t) ∙ rat+rat (fst 1₊) (fst 1₊))
      (normℂ≤twiceModulusℂ (expℂ (unitCircleLogarithmicLift t)))

-- One counterclockwise turn, parameterized by angle on the ordered interval
-- [0,2π]. This is an actual differentiable path with its tangent certified.
unitCircleComplexPath : UniformComplexPath 0ℝ twoPiℝ
unitCircleComplexPath = exponentialComplexPath (verticalComplexPath 0ℝ twoPiℝ ordered) (1₊ +₊ 1₊) circleExponentialBound

unitCircleStartsAtOne : pathStart unitCircleComplexPath ≡ 1ℂ
unitCircleStartsAtOne = expℂ-zero

unitCircleFinishesAtOne : pathFinish unitCircleComplexPath ≡ 1ℂ
unitCircleFinishesAtOne = expℂ-imaginaryTwoPi

unitCircleComplexPathIsClosed : pathFinish unitCircleComplexPath ≡ pathStart unitCircleComplexPath
unitCircleComplexPathIsClosed = unitCircleFinishesAtOne ∙ sym unitCircleStartsAtOne

unitCircleReciprocal : ℝ → ℂ
unitCircleReciprocal = reciprocalAlongLogarithmicLift unitCircleLogarithmicLift

unitCircleReciprocalLaw : ∀ t → UniformComplexPath.curve unitCircleComplexPath t ·ℂ unitCircleReciprocal t ≡ 1ℂ
unitCircleReciprocalLaw t = expℂ-neg-inverse (unitCircleLogarithmicLift t)

-- The lift changes by 2πi even though the curve closes. Consequently this
-- reciprocal integral is nonzero. No global logarithm or circle equivalence
-- is assumed, and the result is not yet a homotopy/winding theorem.
unitCircleReciprocalHasIntegral : HasComplexLineIntegralAlong unitCircleReciprocal unitCircleComplexPath (0ℝ , twoPiℝ)
unitCircleReciprocalHasIntegral = subst (HasComplexLineIntegralAlong unitCircleReciprocal unitCircleComplexPath)
  (ℂ≡ (subZero 0ℝ) (subZero twoPiℝ))
  (logarithmicLiftHasComplexLineIntegral unitCircleComplexPath unitCircleLogarithmicLift (λ t lo hi → refl)
    (pathIsRadiuswiseUniformlyContinuous (verticalComplexPath 0ℝ twoPiℝ ordered)))

unitCircleReciprocalIntegralNonzero : (0ℝ , twoPiℝ) ≡ 0ℂ → ⊥
unitCircleReciprocalIntegralNonzero zero = <ℝ-irrefl 0ℝ (subst (0ℝ <ℝ_) (cong im zero) twoPiℝ-positive)
