module Cubical.Analysis.Real.Order.Strict.Slack where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (subAddCancel; negSub)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition

open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference

opaque
  positiveSlack : ∀ (slack : ℚ₊) →
    0ℝ <ℝ rat (fst slack)
  positiveSlack slack =
    <ℚ→<ℝ (ℚ.fromNat 0) (fst slack) (snd slack)


  rightSlack : ∀ (target : ℝ) (slack : ℚ₊) →
    target <ℝ target + rat (fst slack)
  rightSlack target slack =
    subst (_<ℝ target + rat (fst slack)) (addIdR target)
      (<ℝ-addL 0ℝ (rat (fst slack)) target
        (positiveSlack slack))


  leftSlack : ∀ (target : ℝ) (slack : ℚ₊) →
    target - rat (fst slack) <ℝ target
  leftSlack target slack =
    subst2 _<ℝ_
      (addIdR (target - rat (fst slack)))
      (subAddCancel target (rat (fst slack)))
      (<ℝ-addL 0ℝ (rat (fst slack))
        (target - rat (fst slack))
        (positiveSlack slack))


  slackBand : ∀ (target : ℝ) (slack : ℚ₊) →
    target - rat (fst slack) <ℝ target + rat (fst slack)
  slackBand target slack =
    <ℝ-trans
      (target - rat (fst slack)) target
      (target + rat (fst slack))
      (leftSlack target slack)
      (rightSlack target slack)


private
  addSubtractLeft : ∀ x y → (x + y) - x ≡ y
  addSubtractLeft x y =
    cong (_- x) (addComm x y)
    ∙ sym (addAssoc y x (- x))
    ∙ cong (y +_) (addInvR x)
    ∙ addIdR y

  addSubtractSwap : ∀ x y z → (x + y) - z ≡ (x - z) + y
  addSubtractSwap x y z =
    sym (addAssoc x y (- z))
    ∙ cong (x +_) (addComm y (- z))
    ∙ addAssoc x (- z) y


-- A slack bracket whose endpoint images are one slack apart already gives
-- an approximate preimage at its left endpoint, with error two slacks.
opaque
  slackBracketImagesClose : ∀ lower upper target (slack : ℚ₊) →
    lower <ℝ target + rat (fst slack) →
    target - rat (fst slack) <ℝ upper →
    absℝ (upper - lower) <ℝ rat (fst slack) →
    lower ∼[ slack +₊ slack ] target
  slackBracketImagesClose lower upper target slack below above small =
    absDifference<→closeness lower target (slack +₊ slack)
      (subst2 _<ℝ_
        (sym (absAsMax (lower - target)))
        (rat+rat (fst slack) (fst slack))
        (maxStrictUpper (lower - target) (- (lower - target))
          (s + s) forward backward))
    where
    s : ℝ
    s = rat (fst slack)

    forward : lower - target <ℝ s + s
    forward =
      <ℝ-trans (lower - target) s (s + s)
        (subst ((lower - target) <ℝ_)
          (addSubtractLeft target s)
          (<ℝ-addR lower (target + s) (- target) below))
        (rightSlack s slack)

    targetUpper : target <ℝ upper + s
    targetUpper =
      subst (_<ℝ upper + s) (subAddCancel target s)
        (<ℝ-addR (target - s) upper s above)

    backward : - (lower - target) <ℝ s + s
    backward =
      subst (_<ℝ s + s) (sym (negSub lower target))
        (<ℝ-trans (target - lower) ((upper - lower) + s) (s + s)
          (subst ((target - lower) <ℝ_)
            (addSubtractSwap upper s lower)
            (<ℝ-addR target (upper + s) (- lower) targetUpper))
          (<ℝ-addR (upper - lower) s s
            (≤<ℝ-trans (upper - lower) (absℝ (upper - lower)) s
              (leAbs (upper - lower)) small)))
