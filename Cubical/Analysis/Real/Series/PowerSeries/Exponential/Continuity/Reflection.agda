module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_₊／₊_; ·／)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (negSub)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order

open PositiveRationals using (ℚ₊)


private
  opaque
    productNonnegative : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → 0ℝ ≤ℝ x · y
    productNonnegative x y nonnegative-x nonnegative-y =
      isNonnegative→0≤ (x · y)
        (mulPresIsNonnegative x y
          (0≤→isNonnegative x nonnegative-x)
          (0≤→isNonnegative y nonnegative-y))

    cancelKnownInverse : ∀ inverse coefficient value →
      inverse · coefficient ≡ 1ℝ → inverse · (coefficient · value) ≡ value
    cancelKnownInverse inverse coefficient value cancel =
      mulAssoc inverse coefficient value
      ∙ cong (_· value) cancel ∙ mulIdL value

    -- A nonnegative target bounds a directed difference once it bounds the
    -- ordered case.  Locatedness avoids deciding which endpoint is larger.
    directedBoundFromOrderedCase : ∀ x y bound → 0ℝ ≤ℝ bound →
      (x ≤ℝ y → y - x ≤ℝ bound) → y - x ≤ℝ bound
    directedBoundFromOrderedCase x y bound nonnegative ordered-case =
      notGreater→≤ℝ (y - x) bound λ too-large →
        ≤ℝ→≯ (y - x) bound
          (ordered-case
            (<ℝ-weaken x y
              (positiveSub→< x y
                (≤<ℝ-trans 0ℝ bound (y - x) nonnegative too-large))))
          too-large

    directedExponentialInverseBound : ∀ a x y → a ≤ℝ x →
      y - x ≤ℝ exponentialEntireValue (- a) ·
        absℝ (exponentialEntireValue y - exponentialEntireValue x)
    directedExponentialInverseBound a x y a≤x =
      directedBoundFromOrderedCase x y
        (inverse · absℝ image-difference)
        (productNonnegative inverse (absℝ image-difference)
          (exponentialEntireValue-nonnegative (- a)) (absNonnegative image-difference))
        ordered-case
      where
      inverse : ℝ
      inverse = exponentialEntireValue (- a)

      image-difference : ℝ
      image-difference = exponentialEntireValue y - exponentialEntireValue x

      ordered-case : x ≤ℝ y → y - x ≤ℝ inverse · absℝ image-difference
      ordered-case x≤y =
        subst (_≤ℝ inverse · absℝ image-difference)
          (cancelKnownInverse inverse (exponentialEntireValue a) (y - x)
            (mulComm inverse (exponentialEntireValue a)
            ∙ exponentialEntireValue-mul-negative a))
          (mulPres≤L (exponentialEntireValue a · (y - x))
            (absℝ image-difference) inverse
            (0≤→isNonnegative inverse (exponentialEntireValue-nonnegative (- a)))
            (≤ℝ-trans (exponentialEntireValue a · (y - x)) image-difference
              (absℝ image-difference)
              (≤ℝ-trans (exponentialEntireValue a · (y - x))
                (exponentialEntireValue x · (y - x)) image-difference
                (mulPres≤R-0≤ (exponentialEntireValue a) (exponentialEntireValue x)
                  (y - x) (nonnegativeSub x y x≤y)
                  (exponentialEntireValue-preserves≤ a x a≤x))
                (exponentialEntireValue-lowerDifferenceBound x y x≤y))
              (leAbs image-difference)))


opaque
  exponentialEntireValue-inverseDifferenceBound : ∀ a x y →
    a ≤ℝ x → a ≤ℝ y →
    absℝ (x - y) ≤ℝ exponentialEntireValue (- a) ·
      absℝ (exponentialEntireValue x - exponentialEntireValue y)
  exponentialEntireValue-inverseDifferenceBound a x y a≤x a≤y =
    absLeastUpperBound (x - y)
      (exponentialEntireValue (- a) ·
        absℝ (exponentialEntireValue x - exponentialEntireValue y))
      (directedExponentialInverseBound a y x a≤y)
      (subst2 _≤ℝ_
        (sym (negSub x y))
        (cong (exponentialEntireValue (- a) ·_)
          (absSubComm (exponentialEntireValue y) (exponentialEntireValue x)))
        (directedExponentialInverseBound a x y a≤x))


private
  opaque
    reflectClosenessAtBound : ∀ a (bound : ℚ₊) →
      exponentialEntireValue (- a) ≤ℝ rat (fst bound) →
      ∀ x y → a ≤ℝ x → a ≤ℝ y → ∀ ε →
      exponentialEntireValue x ∼[ ε ₊／₊ bound ] exponentialEntireValue y →
      x ∼[ ε ] y
    reflectClosenessAtBound a bound inverse≤bound x y a≤x a≤y ε near =
      absDifference<→closeness x y ε
        (≤<ℝ-trans (absℝ (x - y))
          (rat (fst bound) · absℝ image-difference) (rat (fst ε))
          (≤ℝ-trans (absℝ (x - y))
            (exponentialEntireValue (- a) · absℝ image-difference)
            (rat (fst bound) · absℝ image-difference)
            (exponentialEntireValue-inverseDifferenceBound a x y a≤x a≤y)
            (mulPres≤R-0≤ (exponentialEntireValue (- a)) (rat (fst bound))
              (absℝ image-difference) (absNonnegative image-difference) inverse≤bound))
          (subst ((rat (fst bound) · absℝ image-difference) <ℝ_)
            (mul-rat (fst bound) (fst (ε ₊／₊ bound)) ∙ cong rat (·／ bound ε))
            (mulPres<PosL (absℝ image-difference)
              (rat (fst (ε ₊／₊ bound))) (rat (fst bound))
              (<ℚ→<ℝ 0 (fst bound) (snd bound))
              (closeness→absDifference< (exponentialEntireValue x)
                (exponentialEntireValue y) (ε ₊／₊ bound) near))))
      where
      image-difference : ℝ
      image-difference = exponentialEntireValue x - exponentialEntireValue y


exponentialEntireValueClosenessReflectionAbove : ∀ a ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ x y → a ≤ℝ x → a ≤ℝ y →
      exponentialEntireValue x ∼[ δ ] exponentialEntireValue y → x ∼[ ε ] y)
exponentialEntireValueClosenessReflectionAbove a ε =
  PT.map (λ { (n , bounded) →
    (ε ₊／₊ naturalBound n)
    , λ x y a≤x a≤y → reflectClosenessAtBound a (naturalBound n)
        (<ℝ-weaken (exponentialEntireValue (- a)) (rat (naturalRational n)) bounded)
        x y a≤x a≤y ε })
    (∃naturalUpperBound (exponentialEntireValue (- a)))

exponentialEntireValueClosenessReflectionOnInterval : ∀ a b ε →
  ∃[ δ ∈ ℚ₊ ]
    (∀ (x y : ClosedInterval a b) →
      exponentialEntireValue (fst x) ∼[ δ ] exponentialEntireValue (fst y) →
      fst x ∼[ ε ] fst y)
exponentialEntireValueClosenessReflectionOnInterval a b ε =
  PT.map (λ { (δ , reflects) →
    δ , λ x y → reflects (fst x) (fst y) (fst (snd x)) (fst (snd y)) })
    (exponentialEntireValueClosenessReflectionAbove a ε)
