module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition


-- Double-angle formulas ----------------------------------------------

opaque
  sinℝ-double : ∀ x →
    sinℝ (x + x)
      ≡ (sinℝ x · cosℝ x) + (sinℝ x · cosℝ x)
  sinℝ-double x =
      sinℝ-add x x
    ∙ cong ((sinℝ x · cosℝ x) +_)
        (mulComm (cosℝ x) (sinℝ x))


  cosℝ-double : ∀ x →
    cosℝ (x + x)
      ≡ (cosℝ x · cosℝ x) - (sinℝ x · sinℝ x)
  cosℝ-double x = cosℝ-add x x


-- The following two purely additive rearrangements expose the total
-- square C + S.  They use only named abelian-group laws.

private
  opaque
    cosine-as-total-minus-double-sine : ∀ cosine-square sine-square →
      cosine-square - sine-square
        ≡
      (cosine-square + sine-square) -
        (sine-square + sine-square)
    cosine-as-total-minus-double-sine cosine-square sine-square =
      cong (cosine-square +_)
        (sym (addIdL (- sine-square)))
      ∙ cong (λ middle → cosine-square + (middle + (- sine-square)))
          (sym (addInvR sine-square))
      ∙ cong (cosine-square +_)
          (sym (addAssoc sine-square (- sine-square) (- sine-square)))
      ∙ addAssoc
          cosine-square sine-square ((- sine-square) + (- sine-square))
      ∙ cong ((cosine-square + sine-square) +_)
          (sym (negAdd sine-square sine-square))


    cosine-as-double-cosine-minus-total : ∀ cosine-square sine-square →
      cosine-square - sine-square
        ≡
      (cosine-square + cosine-square) -
        (cosine-square + sine-square)
    cosine-as-double-cosine-minus-total cosine-square sine-square =
      cong (cosine-square +_)
        (sym (addIdL (- sine-square)))
      ∙ cong (λ middle → cosine-square + (middle + (- sine-square)))
          (sym (addInvR cosine-square))
      ∙ cong (cosine-square +_)
          (sym (addAssoc cosine-square (- cosine-square) (- sine-square)))
      ∙ addAssoc
          cosine-square cosine-square
          ((- cosine-square) + (- sine-square))
      ∙ cong ((cosine-square + cosine-square) +_)
          (sym (negAdd cosine-square sine-square))


    cosSquare-add-sinSquare≡one : ∀ x →
      cosℝ x · cosℝ x + sinℝ x · sinℝ x ≡ 1ℝ
    cosSquare-add-sinSquare≡one x =
      addComm
        (cosℝ x · cosℝ x)
        (sinℝ x · sinℝ x)
      ∙ sin²+cos²≡1 x


-- Pythagorean rewrites of the cosine double angle --------------------

opaque
  cosℝ-double≡one-sub-doubleSinSquare : ∀ x →
    cosℝ (x + x)
      ≡ 1ℝ -
        ((sinℝ x · sinℝ x) + (sinℝ x · sinℝ x))
  cosℝ-double≡one-sub-doubleSinSquare x =
      cosℝ-double x
    ∙ cosine-as-total-minus-double-sine
        (cosℝ x · cosℝ x) (sinℝ x · sinℝ x)
    ∙ cong
        (λ total → total -
          ((sinℝ x · sinℝ x) + (sinℝ x · sinℝ x)))
        (cosSquare-add-sinSquare≡one x)


  cosℝ-double≡doubleCosSquare-sub-one : ∀ x →
    cosℝ (x + x)
      ≡ ((cosℝ x · cosℝ x) + (cosℝ x · cosℝ x)) - 1ℝ
  cosℝ-double≡doubleCosSquare-sub-one x =
      cosℝ-double x
    ∙ cosine-as-double-cosine-minus-total
        (cosℝ x · cosℝ x) (sinℝ x · sinℝ x)
    ∙ cong
        (λ total →
          ((cosℝ x · cosℝ x) + (cosℝ x · cosℝ x)) - total)
        (cosSquare-add-sinSquare≡one x)
