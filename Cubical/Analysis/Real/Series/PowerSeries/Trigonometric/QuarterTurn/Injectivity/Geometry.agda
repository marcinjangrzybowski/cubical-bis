module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Rationals.Base using ([_/_])
import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma using (_×_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Laws
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


quarterTurnHalf : ℚ
quarterTurnHalf = [ pos 1 / 1+ 1 ]


quarterTurnMidpoint : ℝ → ℝ → ℝ
quarterTurnMidpoint x y = quarterTurnHalf ⋆ (x + y)


quarterTurnHalfDifference : ℝ → ℝ → ℝ
quarterTurnHalfDifference x y = quarterTurnHalf ⋆ (y - x)


opaque
  quarterTurnHalf-positive : 0ℝ <ℝ rat quarterTurnHalf
  quarterTurnHalf-positive =
    <ℚ→<ℝ (ℚ.fromNat 0) quarterTurnHalf 1/2∈ℚ.0<1/2


  quarterTurnHalf-nonnegative : 0ℝ ≤ℝ rat quarterTurnHalf
  quarterTurnHalf-nonnegative =
    <ℝ-weaken 0ℝ (rat quarterTurnHalf)
      quarterTurnHalf-positive


  quarterTurnHalfScalar-zero :
    quarterTurnHalf ⋆ 0ℝ ≡ 0ℝ
  quarterTurnHalfScalar-zero =
    scalar-as-mul quarterTurnHalf 0ℝ
    ∙ ℝRing.0RightAnnihilates (rat quarterTurnHalf)


  quarterTurnHalfScalar-pres< : ∀ {x y : ℝ} →
    x <ℝ y →
    quarterTurnHalf ⋆ x <ℝ quarterTurnHalf ⋆ y
  quarterTurnHalfScalar-pres< {x} {y} x<y =
    subst2 _<ℝ_
      (sym (scalar-as-mul quarterTurnHalf x))
      (sym (scalar-as-mul quarterTurnHalf y))
      (mulPres<PosL x y (rat quarterTurnHalf)
        quarterTurnHalf-positive x<y)


  quarterTurnHalfScalar-pres≤ : ∀ {x y : ℝ} →
    x ≤ℝ y →
    quarterTurnHalf ⋆ x ≤ℝ quarterTurnHalf ⋆ y
  quarterTurnHalfScalar-pres≤ {x} {y} x≤y =
    subst2 _≤ℝ_
      (sym (scalar-as-mul quarterTurnHalf x))
      (sym (scalar-as-mul quarterTurnHalf y))
      (mulPres≤L x y (rat quarterTurnHalf)
        (0≤→isNonnegative
          (rat quarterTurnHalf) quarterTurnHalf-nonnegative)
        x≤y)


  quarterTurnHalfScalar-double : ∀ (x : ℝ) →
    quarterTurnHalf ⋆ (x + x) ≡ x
  quarterTurnHalfScalar-double x =
    scalar-dist-right quarterTurnHalf x x
    ∙ sym (scalar-dist-left quarterTurnHalf quarterTurnHalf x)
    ∙ cong (_⋆ x) 1/2∈ℚ.1/2+1/2≡1
    ∙ scalar-id x


  quarterTurnHalfDifference-double : ∀ (x y : ℝ) →
    quarterTurnHalfDifference x y +
      quarterTurnHalfDifference x y
      ≡ y - x
  quarterTurnHalfDifference-double x y =
    sym
      (scalar-dist-left
        quarterTurnHalf quarterTurnHalf (y - x))
    ∙ cong (_⋆ (y - x)) 1/2∈ℚ.1/2+1/2≡1
    ∙ scalar-id (y - x)


private
  midpoint-plus-difference-inner : ∀ (x y : ℝ) →
    (x + y) + (y - x) ≡ y + y
  midpoint-plus-difference-inner x y =
    cong (_+ (y - x)) (addComm x y)
    ∙ ℝRing.+ShufflePairs y x y (- x)
    ∙ cong ((y + y) +_) (addInvR x)
    ∙ addIdR (y + y)


  subtract-difference : ∀ (x y : ℝ) →
    y - (y - x) ≡ x
  subtract-difference x y =
    cong (y +_)
      (sym (ℝRing.-Dist y (- x)))
    ∙ addAssoc y (- y) (- (- x))
    ∙ cong (_+ (- (- x))) (addInvR y)
    ∙ addIdL (- (- x))
    ∙ negInvol x


opaque
  quarterTurnMidpoint-plusHalfDifference : ∀ (x y : ℝ) →
    quarterTurnMidpoint x y +
      quarterTurnHalfDifference x y
      ≡ y
  quarterTurnMidpoint-plusHalfDifference x y =
    sym
      (scalar-dist-right quarterTurnHalf
        (x + y) (y - x))
    ∙ cong (quarterTurnHalf ⋆_)
        (midpoint-plus-difference-inner x y)
    ∙ quarterTurnHalfScalar-double y


  quarterTurnMidpoint-plusNegativeHalfDifference : ∀ (x y : ℝ) →
    quarterTurnMidpoint x y +
      (- quarterTurnHalfDifference x y)
      ≡ x
  quarterTurnMidpoint-plusNegativeHalfDifference x y =
    ℝRing.translatedDifference
      (quarterTurnHalfDifference x y)
      (quarterTurnMidpoint x y)
      (quarterTurnHalfDifference x y)
    ∙ cong₂ _-_
        (addComm
          (quarterTurnHalfDifference x y)
          (quarterTurnMidpoint x y)
        ∙ quarterTurnMidpoint-plusHalfDifference x y)
        (quarterTurnHalfDifference-double x y)
    ∙ subtract-difference x y


opaque
  quarterTurnHalfDifference-positive : ∀ (x y : ℝ) →
    x <ℝ y →
    0ℝ <ℝ quarterTurnHalfDifference x y
  quarterTurnHalfDifference-positive x y x<y =
    subst (_<ℝ quarterTurnHalfDifference x y)
      (quarterTurnHalfScalar-zero)
      (quarterTurnHalfScalar-pres<
        {x = 0ℝ} {y = y - x}
        (positiveSub x y x<y))

