module Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Keep the algebra on real variables behind small opaque boundaries.  The
-- clients substitute partition nodes and integral values only afterwards.
opaque
  differenceThrough : ∀ x y z → (x - z) - (y - z) ≡ x - y
  differenceThrough x y z =
    differenceOfSums x (- z) y (- z)
    ∙ cong ((x - y) +_) (subSelf (- z))
    ∙ addIdR (x - y)

  differenceOfDifferences : ∀ a b c d →
    (a - b) - (c - d) ≡ (a - c) - (b - d)
  differenceOfDifferences a b c d =
    differenceOfSums a (- b) c (- d)
    ∙ cong ((a - c) +_) (differenceOfNegatives b d)

  remainderThrough : ∀ Fx Fy Fz c x y z →
    ((Fy - Fz) - c · (y - z)) - ((Fx - Fz) - c · (x - z))
      ≡ (Fy - Fx) - c · (y - x)
  remainderThrough Fx Fy Fz c x y z =
    differenceOfDifferences (Fy - Fz) (c · (y - z))
      (Fx - Fz) (c · (x - z))
    ∙ cong₂ _-_
        (differenceThrough Fy Fx Fz)
        (sym (ℝRing.·DistR- c (y - z) (x - z))
          ∙ cong (c ·_) (differenceThrough y x z))

  splitDifference : ∀ x y z → (y - z) + (z - x) ≡ y - x
  splitDifference x y z =
    addAssoc (y - z) z (- x)
    ∙ cong (_+ (- x)) (subAddCancel y z)
