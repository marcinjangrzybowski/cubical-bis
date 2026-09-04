module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Slack where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition


opaque
  sineQuarter-positiveSlack : ∀ (slack : ℚ₊) →
    0ℝ <ℝ rat (fst slack)
  sineQuarter-positiveSlack slack =
    <ℚ→<ℝ (ℚ.fromNat 0) (fst slack) (snd slack)


  sineQuarter-rightSlack : ∀ (target : ℝ) (slack : ℚ₊) →
    target <ℝ target + rat (fst slack)
  sineQuarter-rightSlack target slack =
    subst (_<ℝ target + rat (fst slack)) (addIdR target)
      (<ℝ-addL 0ℝ (rat (fst slack)) target
        (sineQuarter-positiveSlack slack))


  sineQuarter-leftSlack : ∀ (target : ℝ) (slack : ℚ₊) →
    target - rat (fst slack) <ℝ target
  sineQuarter-leftSlack target slack =
    subst2 _<ℝ_
      (addIdR (target - rat (fst slack)))
      (subAddCancel target (rat (fst slack)))
      (<ℝ-addL 0ℝ (rat (fst slack))
        (target - rat (fst slack))
        (sineQuarter-positiveSlack slack))
    where
    subAddCancel : ∀ x y → (x - y) + y ≡ x
    subAddCancel x y =
      sym (addAssoc x (- y) y)
      ∙ cong (x +_) (addInvL y)
      ∙ addIdR x


  sineQuarter-slackBand : ∀ (target : ℝ) (slack : ℚ₊) →
    target - rat (fst slack) <ℝ target + rat (fst slack)
  sineQuarter-slackBand target slack =
    <ℝ-trans
      (target - rat (fst slack)) target
      (target + rat (fst slack))
      (sineQuarter-leftSlack target slack)
      (sineQuarter-rightSlack target slack)
