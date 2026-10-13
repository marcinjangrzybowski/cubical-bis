module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.SmallAngle where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Consequences
open import Cubical.Analysis.Real.Series.Geometric.Rational using (halfℚ; halfℚPath)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.BaseInterval

private
  opaque
    lowerFromZero : ∀ F f d → F 0ℝ ≡ 0ℝ →
      IsRadiuswiseUniformDerivative F f →
      (∀ z → 0ℝ ≤ℝ z → z ≤ℝ 1ℝ → d ≤ℝ f z) →
      ∀ x → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ → x · d ≤ℝ F x
    lowerFromZero F f d at-zero derivative bounded x nonnegative upper =
      subst2 _≤ℝ_
        (cong (_· d) (subZero x))
        (cong (λ z → F x - z) at-zero ∙ subZero (F x))
        (uniformDerivativeLowerBoundOn F f 0ℝ 1ℝ d
          (radiuswiseUniformDerivative→onInterval F f 0ℝ 1ℝ derivative)
          bounded 0ℝ x (≤ℝ-refl 0ℝ) nonnegative upper)

    rationalHalf : ∀ (q : ℚ₊) → rat (fst q) · rat halfℚ ≡ rat (fst (q /2₊))
    rationalHalf q = cong (rat (fst q) ·_) (cong rat halfℚPath)
      ∙ mul-rat (fst q) _

opaque
  sinℝ-halfLowerBound : ∀ x → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    x · rat halfℚ ≤ℝ sinℝ x
  sinℝ-halfLowerBound = lowerFromZero sinℝ cosℝ (rat halfℚ)
    sinℝ-zero sinℝHasUniformDerivative half≤cosℝ-onUnitInterval

  sinℝ-rationalHalfLowerBound : ∀ (q : ℚ₊) →
    rat (fst q) ≤ℝ 1ℝ → rat (fst (q /2₊)) ≤ℝ sinℝ (rat (fst q))
  sinℝ-rationalHalfLowerBound q q≤one =
    subst {x = rat (fst q) · rat halfℚ} {y = rat (fst (q /2₊))}
      (_≤ℝ sinℝ (rat (fst q))) (rationalHalf q)
      (sinℝ-halfLowerBound (rat (fst q))
        (<ℝ-weaken 0ℝ (rat (fst q)) (<ℚ→<ℝ 0 (fst q) (snd q))) q≤one)
