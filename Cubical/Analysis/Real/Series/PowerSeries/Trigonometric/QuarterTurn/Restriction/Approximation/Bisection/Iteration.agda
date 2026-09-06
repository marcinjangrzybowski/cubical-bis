module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Iteration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Step
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Width


-- Only finitely many located comparisons are made for a requested depth.
-- In particular this theorem does not select a countable family of branches.
sineQuarterSlackBracketRefine : ∀ quarter target slack →
  (bracket : SineQuarterSlackBracket quarter target slack) → ∀ n →
  ∥ Σ[ refined ∈ SineQuarterSlackBracket quarter target slack ]
      sineQuarterBracketWidth quarter target slack refined ≡
      iteratedHalving n
        (sineQuarterBracketWidth quarter target slack bracket) ∥₁
sineQuarterSlackBracketRefine quarter target slack bracket zero =
  ∣ bracket , refl ∣₁
sineQuarterSlackBracketRefine quarter target slack bracket (suc n) =
  PT.rec squash₁
    (λ { (previous , previous-width) →
      PT.map
        (λ { (refined , refined-width) →
          refined , refined-width
            ∙ cong (quarterTurnHalf ⋆_) previous-width })
        (sineQuarterSlackBracketStep quarter target slack previous) })
    (sineQuarterSlackBracketRefine quarter target slack bracket n)


sineQuarterSlackBracketArbitrarilySmall : ∀ quarter target slack →
  SineQuarterSlackBracket quarter target slack → ∀ (tolerance : ℚ₊) →
  ∥ Σ[ refined ∈ SineQuarterSlackBracket quarter target slack ]
      sineQuarterBracketWidth quarter target slack refined
        <ℝ rat (fst tolerance) ∥₁
sineQuarterSlackBracketArbitrarilySmall
    quarter target slack bracket tolerance =
  PT.rec squash₁
    (λ { (n , small) →
      PT.map
        (λ { (refined , width) →
          refined , subst (_<ℝ rat (fst tolerance)) (sym width) small })
        (sineQuarterSlackBracketRefine quarter target slack bracket n) })
    (iteratedHalvingEventuallySmall
      (sineQuarterBracketWidth quarter target slack bracket) tolerance)
