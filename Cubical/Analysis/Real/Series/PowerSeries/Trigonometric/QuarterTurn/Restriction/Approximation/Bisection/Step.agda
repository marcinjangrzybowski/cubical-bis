module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Step where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Geometry
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Comparison


sineQuarterBracketWidth : ∀ quarter target slack →
  SineQuarterSlackBracket quarter target slack → ℝ
sineQuarterBracketWidth quarter target slack (left , right , _) =
  fst right - fst left


private
  addSubtractCancel : ∀ x y → (x + y) - y ≡ x
  addSubtractCancel x y =
    sym (addAssoc x y (- y))
    ∙ cong (x +_) (addInvR y)
    ∙ addIdR x


opaque
  sineQuarter-midpoint-rightWidth : ∀ left right →
    right - quarterTurnMidpoint left right ≡
    quarterTurnHalfDifference left right
  sineQuarter-midpoint-rightWidth left right =
    cong (_- quarterTurnMidpoint left right)
      (sym (quarterTurnMidpoint-plusHalfDifference left right))
    ∙ cong (_- quarterTurnMidpoint left right)
        (addComm (quarterTurnMidpoint left right)
          (quarterTurnHalfDifference left right))
    ∙ addSubtractCancel (quarterTurnHalfDifference left right)
        (quarterTurnMidpoint left right)


  sineQuarter-midpoint-leftWidth : ∀ left right →
    quarterTurnMidpoint left right - left ≡
    quarterTurnHalfDifference left right
  sineQuarter-midpoint-leftWidth left right =
    cong (quarterTurnMidpoint left right +_)
      (cong -_
        (sym (quarterTurnMidpoint-plusNegativeHalfDifference left right)))
    ∙ cong (quarterTurnMidpoint left right +_)
        (negAdd (quarterTurnMidpoint left right)
          (- quarterTurnHalfDifference left right)
        ∙ cong ((- quarterTurnMidpoint left right) +_)
            (negInvol (quarterTurnHalfDifference left right)))
    ∙ addAssoc (quarterTurnMidpoint left right)
        (- quarterTurnMidpoint left right)
        (quarterTurnHalfDifference left right)
    ∙ cong (_+ quarterTurnHalfDifference left right)
        (addInvR (quarterTurnMidpoint left right))
    ∙ addIdL (quarterTurnHalfDifference left right)


-- The branch is only chosen under propositional truncation.  Both choices
-- preserve the slack inequalities and halve the width exactly.
sineQuarterSlackBracketStep : ∀ quarter target slack →
  (bracket : SineQuarterSlackBracket quarter target slack) →
  ∥ Σ[ refined ∈ SineQuarterSlackBracket quarter target slack ]
      sineQuarterBracketWidth quarter target slack refined ≡
      quarterTurnHalf ⋆ sineQuarterBracketWidth quarter target slack bracket ∥₁
sineQuarterSlackBracketStep quarter target slack
    (left , right , left≤right , lower , upper) =
  PT.map refine
    (sineQuarterSlackMidpointComparison target (fst middle) slack)
  where
  midpoint : ℝ
  midpoint = quarterTurnMidpoint (fst left) (fst right)

  left≤midpoint : fst left ≤ℝ midpoint
  left≤midpoint =
    sineQuarter-midpoint-lower (fst left) (fst right) left≤right

  midpoint≤right : midpoint ≤ℝ fst right
  midpoint≤right =
    sineQuarter-midpoint-upper (fst left) (fst right) left≤right

  middle : SineQuarterInterval quarter
  middle = midpoint
    , ≤ℝ-trans (- quarter) (fst left) midpoint
        (fst (snd left)) left≤midpoint
    , ≤ℝ-trans midpoint (fst right) quarter
        midpoint≤right (snd (snd right))

  refine :
    (target - rat (fst slack) <ℝ sinℝ (fst middle))
      ⊎ (sinℝ (fst middle) <ℝ target + rat (fst slack)) →
    Σ[ refined ∈ SineQuarterSlackBracket quarter target slack ]
      sineQuarterBracketWidth quarter target slack refined ≡
      quarterTurnHalf ⋆ (fst right - fst left)
  refine (inl above) =
    (left , middle , left≤midpoint , lower , above)
    , sineQuarter-midpoint-leftWidth (fst left) (fst right)
  refine (inr below) =
    (middle , right , midpoint≤right , below , upper)
    , sineQuarter-midpoint-rightWidth (fst left) (fst right)
