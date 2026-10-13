module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities.Products where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Algebra
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Formula

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  opaque
    sumAfterSigns : ∀ a b → (a + b) + (a - b) ≡ a + a
    sumAfterSigns a b = R.+ShufflePairs a b a (- b)
      ∙ cong ((a + a) +_) (addInvR b) ∙ addIdR (a + a)

    sumAfterReversedSigns : ∀ a b → (a - b) + (a + b) ≡ a + a
    sumAfterReversedSigns a b = addComm (a - b) (a + b) ∙ sumAfterSigns a b

    differenceAfterReversedSigns : ∀ a b → (a - b) - (a + b) ≡ - (b + b)
    differenceAfterReversedSigns a b =
      sym (negInvol ((a - b) - (a + b))) ∙ cong -_
        (sym (R.-Dist (a - b) (- (a + b)))
        ∙ cong (λ z → (- (a - b)) + z) (negInvol (a + b))
        ∙ addComm (- (a - b)) (a + b)
        ∙ twiceAfterDifference a b)

-- The doubled forms avoid division; the following corollaries use the
-- native rational scalar action to express the conventional half factors.
opaque
  cosℝ-product-double : ∀ x y →
    (cosℝ x · cosℝ y) + (cosℝ x · cosℝ y) ≡
    cosℝ (x + (- y)) + cosℝ (x + y)
  cosℝ-product-double x y = sym
    (cong₂ _+_ (cosℝ-sub x y) (cosℝ-add x y)
      ∙ sumAfterSigns (cosℝ x · cosℝ y) (sinℝ x · sinℝ y))

  sinℝ-product-double : ∀ x y →
    (sinℝ x · sinℝ y) + (sinℝ x · sinℝ y) ≡
    cosℝ (x + (- y)) - cosℝ (x + y)
  sinℝ-product-double x y = sym
    (cong₂ _-_ (cosℝ-sub x y) (cosℝ-add x y)
      ∙ twiceAfterDifference (cosℝ x · cosℝ y) (sinℝ x · sinℝ y))

  sinℝ-cosℝ-product-double : ∀ x y →
    (sinℝ x · cosℝ y) + (sinℝ x · cosℝ y) ≡
    sinℝ (x + y) + sinℝ (x + (- y))
  sinℝ-cosℝ-product-double x y = sym
    (cong₂ _+_ (sinℝ-add x y) (sinℝ-sub x y)
      ∙ sumAfterSigns (sinℝ x · cosℝ y) (cosℝ x · sinℝ y))

  cosℝ-sinℝ-product-double : ∀ x y →
    (cosℝ x · sinℝ y) + (cosℝ x · sinℝ y) ≡
    sinℝ (x + y) - sinℝ (x + (- y))
  cosℝ-sinℝ-product-double x y = sym
    (cong₂ _-_ (sinℝ-add x y) (sinℝ-sub x y)
      ∙ twiceAfterDifference (sinℝ x · cosℝ y) (cosℝ x · sinℝ y))

  cosℝ-product-to-sum : ∀ x y → cosℝ x · cosℝ y ≡
    quarterTurnHalf ⋆ (cosℝ (x + (- y)) + cosℝ (x + y))
  cosℝ-product-to-sum x y = sym (quarterTurnHalfScalar-double (cosℝ x · cosℝ y))
    ∙ cong (quarterTurnHalf ⋆_) (cosℝ-product-double x y)

  sinℝ-product-to-sum : ∀ x y → sinℝ x · sinℝ y ≡
    quarterTurnHalf ⋆ (cosℝ (x + (- y)) - cosℝ (x + y))
  sinℝ-product-to-sum x y = sym (quarterTurnHalfScalar-double (sinℝ x · sinℝ y))
    ∙ cong (quarterTurnHalf ⋆_) (sinℝ-product-double x y)

  sinℝ-cosℝ-product-to-sum : ∀ x y → sinℝ x · cosℝ y ≡
    quarterTurnHalf ⋆ (sinℝ (x + y) + sinℝ (x + (- y)))
  sinℝ-cosℝ-product-to-sum x y = sym (quarterTurnHalfScalar-double (sinℝ x · cosℝ y))
    ∙ cong (quarterTurnHalf ⋆_) (sinℝ-cosℝ-product-double x y)

  cosℝ-sinℝ-product-to-sum : ∀ x y → cosℝ x · sinℝ y ≡
    quarterTurnHalf ⋆ (sinℝ (x + y) - sinℝ (x + (- y)))
  cosℝ-sinℝ-product-to-sum x y = sym (quarterTurnHalfScalar-double (cosℝ x · sinℝ y))
    ∙ cong (quarterTurnHalf ⋆_) (cosℝ-sinℝ-product-double x y)

  sinℝ-symmetricSum : ∀ m d → sinℝ (m + d) + sinℝ (m + (- d)) ≡
    (sinℝ m · cosℝ d) + (sinℝ m · cosℝ d)
  sinℝ-symmetricSum m d = sym (sinℝ-cosℝ-product-double m d)

  cosℝ-symmetricSum : ∀ m d → cosℝ (m + d) + cosℝ (m + (- d)) ≡
    (cosℝ m · cosℝ d) + (cosℝ m · cosℝ d)
  cosℝ-symmetricSum m d = cong₂ _+_ (cosℝ-add m d) (cosℝ-sub m d)
    ∙ sumAfterReversedSigns (cosℝ m · cosℝ d) (sinℝ m · sinℝ d)

  cosℝ-symmetricDifference : ∀ m d → cosℝ (m + d) - cosℝ (m + (- d)) ≡
    - ((sinℝ m · sinℝ d) + (sinℝ m · sinℝ d))
  cosℝ-symmetricDifference m d = cong₂ _-_ (cosℝ-add m d) (cosℝ-sub m d)
    ∙ differenceAfterReversedSigns (cosℝ m · cosℝ d) (sinℝ m · sinℝ d)

  sinℝ-sum-to-product : ∀ x y → sinℝ y + sinℝ x ≡
    (sinℝ (quarterTurnMidpoint x y) · cosℝ (quarterTurnHalfDifference x y)) +
    (sinℝ (quarterTurnMidpoint x y) · cosℝ (quarterTurnHalfDifference x y))
  sinℝ-sum-to-product x y = cong₂ _+_
    (cong sinℝ (sym (quarterTurnMidpoint-plusHalfDifference x y)))
    (cong sinℝ (sym (quarterTurnMidpoint-plusNegativeHalfDifference x y)))
    ∙ sinℝ-symmetricSum (quarterTurnMidpoint x y) (quarterTurnHalfDifference x y)

  cosℝ-sum-to-product : ∀ x y → cosℝ y + cosℝ x ≡
    (cosℝ (quarterTurnMidpoint x y) · cosℝ (quarterTurnHalfDifference x y)) +
    (cosℝ (quarterTurnMidpoint x y) · cosℝ (quarterTurnHalfDifference x y))
  cosℝ-sum-to-product x y = cong₂ _+_
    (cong cosℝ (sym (quarterTurnMidpoint-plusHalfDifference x y)))
    (cong cosℝ (sym (quarterTurnMidpoint-plusNegativeHalfDifference x y)))
    ∙ cosℝ-symmetricSum (quarterTurnMidpoint x y) (quarterTurnHalfDifference x y)

  cosℝ-difference-to-product : ∀ x y → cosℝ y - cosℝ x ≡
    - ((sinℝ (quarterTurnMidpoint x y) · sinℝ (quarterTurnHalfDifference x y)) +
       (sinℝ (quarterTurnMidpoint x y) · sinℝ (quarterTurnHalfDifference x y)))
  cosℝ-difference-to-product x y = cong₂ _-_
    (cong cosℝ (sym (quarterTurnMidpoint-plusHalfDifference x y)))
    (cong cosℝ (sym (quarterTurnMidpoint-plusNegativeHalfDifference x y)))
    ∙ cosℝ-symmetricDifference (quarterTurnMidpoint x y) (quarterTurnHalfDifference x y)
