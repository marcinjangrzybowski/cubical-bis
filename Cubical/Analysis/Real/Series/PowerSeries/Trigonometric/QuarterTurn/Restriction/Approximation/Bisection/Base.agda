module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


-- A finite bisection uses overlapping comparisons rather than deciding the
-- exact order of the midpoint image and the target.  The overlap is the
-- positive rational `slack`.  The lightweight sigma boundary avoids record
-- projection normalization over proof-dependent interval endpoints.

SineQuarterSlackBracket : ℝ → ℝ → ℚ₊ → Type₀
SineQuarterSlackBracket quarter target slack =
  Σ[ left ∈ SineQuarterInterval quarter ]
  Σ[ right ∈ SineQuarterInterval quarter ]
    (fst left ≤ℝ fst right)
    × (sinℝ (fst left) <ℝ target + rat (fst slack))
    × (target - rat (fst slack) <ℝ sinℝ (fst right))
