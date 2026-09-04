module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean


square≤one→abs≤one : ∀ x →
  x · x ≤ℝ 1ℝ → absℝ x ≤ℝ 1ℝ
square≤one→abs≤one x square≤one =
  notGreater→≤ℝ (absℝ x) 1ℝ λ one<abs →
    ≤ℝ→≯ (x · x) 1ℝ square≤one
      (subst2 _<ℝ_
        (mulIdL 1ℝ)
        (absSquared x)
        (mulPres<
          1ℝ (absℝ x) 1ℝ (absℝ x)
          (<ℝ-trans 0ℝ 1ℝ (absℝ x)
            (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
            one<abs)
          (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
          one<abs one<abs))


sinℝ-square≤one : ∀ x →
  sinℝ x · sinℝ x ≤ℝ 1ℝ
sinℝ-square≤one x =
  subst2 _≤ℝ_
    (addIdR (sinℝ x · sinℝ x))
    (sin²+cos²≡1 x)
    (addPres≤L
      0ℝ
      (cosℝ x · cosℝ x)
      (sinℝ x · sinℝ x)
      (isNonnegative→0≤
        (cosℝ x · cosℝ x)
        (squareIsNonnegative (cosℝ x))))


cosℝ-square≤one : ∀ x →
  cosℝ x · cosℝ x ≤ℝ 1ℝ
cosℝ-square≤one x =
  subst2 _≤ℝ_
    (addIdL (cosℝ x · cosℝ x))
    (sin²+cos²≡1 x)
    (addPres≤R
      0ℝ
      (sinℝ x · sinℝ x)
      (cosℝ x · cosℝ x)
      (isNonnegative→0≤
        (sinℝ x · sinℝ x)
        (squareIsNonnegative (sinℝ x))))


sinℝ-abs≤one : ∀ x →
  absℝ (sinℝ x) ≤ℝ 1ℝ
sinℝ-abs≤one x =
  square≤one→abs≤one (sinℝ x) (sinℝ-square≤one x)


cosℝ-abs≤one : ∀ x →
  absℝ (cosℝ x) ≤ℝ 1ℝ
cosℝ-abs≤one x =
  square≤one→abs≤one (cosℝ x) (cosℝ-square≤one x)
