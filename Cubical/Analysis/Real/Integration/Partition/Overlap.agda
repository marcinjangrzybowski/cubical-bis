module Cubical.Analysis.Real.Integration.Partition.Overlap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Lattice
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Domain.Interval

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Closed inequalities admit this case rule because they are equivalent to
-- negations of strict inequalities.  It constructs no ordering decision.
opaque
  orderCasesForBound : ∀ (x y value bound : ℝ) →
    (x ≤ℝ y → value ≤ℝ bound) → (y ≤ℝ x → value ≤ℝ bound) →
    value ≤ℝ bound
  orderCasesForBound x y value bound forward backward =
    notGreater→≤ℝ value bound λ bound<value →
      ≤ℝ→≯ value bound
        (backward (notGreater→≤ℝ y x λ x<y →
          ≤ℝ→≯ value bound (forward (<ℝ-weaken x y x<y)) bound<value))
        bound<value

  orderCasesForPath : ∀ (x y left right : ℝ) →
    (x ≤ℝ y → left ≡ right) → (y ≤ℝ x → left ≡ right) → left ≡ right
  orderCasesForPath x y left right forward backward =
    ≤ℝ-antisym left right
      (orderCasesForBound x y left right
        (λ p → subst (left ≤ℝ_) (forward p) (≤ℝ-refl left))
        (λ p → subst (left ≤ℝ_) (backward p) (≤ℝ-refl left)))
      (orderCasesForBound x y right left
        (λ p → subst (_≤ℝ left) (forward p) (≤ℝ-refl left))
        (λ p → subst (_≤ℝ left) (backward p) (≤ℝ-refl left)))

  clampBelowInterval : ∀ a b x → x ≤ℝ a → clampInterval a b x ≡ a
  clampBelowInterval a b x x≤a =
    maxComm a (minℝ b x)
    ∙ ≤ℝ-trans (minℝ b x) x a (min≤right b x) x≤a

  clampAboveInterval : ∀ a b x → a ≤ℝ b → b ≤ℝ x →
    clampInterval a b x ≡ b
  clampAboveInterval a b x a≤b b≤x =
    cong (maxℝ a)
      (cong (minℝ b) (sym b≤x) ∙ minAbsorbMax b x)
    ∙ a≤b

  clampIntervalMonotone : ∀ a b x y → x ≤ℝ y →
    clampInterval a b x ≤ℝ clampInterval a b y
  clampIntervalMonotone a b x y x≤y =
    maxLeastUpperBound a (minℝ b x) (maxℝ a (minℝ b y))
      (left≤max a (minℝ b y))
      (≤ℝ-trans (minℝ b x) (minℝ b y) (maxℝ a (minℝ b y))
        (minGreatestLowerBound b y (minℝ b x)
          (min≤left b x)
          (≤ℝ-trans (minℝ b x) x y (min≤right b x) x≤y))
        (right≤max a (minℝ b y)))


overlapWidth : ℝ → ℝ → ℝ → ℝ → ℝ
overlapWidth a b c d = clampInterval a b d - clampInterval a b c

opaque
  overlapWidthNonnegative : ∀ a b c d → c ≤ℝ d →
    0ℝ ≤ℝ overlapWidth a b c d
  overlapWidthNonnegative a b c d c≤d =
    nonnegativeSub (clampInterval a b c) (clampInterval a b d)
      (clampIntervalMonotone a b c d c≤d)

  overlapWidthBefore : ∀ a b c d → a ≤ℝ b → b ≤ℝ c → c ≤ℝ d →
    overlapWidth a b c d ≡ 0ℝ
  overlapWidthBefore a b c d a≤b b≤c c≤d =
    cong₂ _-_
      (clampAboveInterval a b d a≤b (≤ℝ-trans b c d b≤c c≤d))
      (clampAboveInterval a b c a≤b b≤c)
    ∙ subSelf b

  overlapWidthAfter : ∀ a b c d → c ≤ℝ d → d ≤ℝ a →
    overlapWidth a b c d ≡ 0ℝ
  overlapWidthAfter a b c d c≤d d≤a =
    cong₂ _-_
      (clampBelowInterval a b d d≤a)
      (clampBelowInterval a b c (≤ℝ-trans c d a c≤d d≤a))
    ∙ subSelf a

  overlapWidthSymmetric : ∀ a b c d → a ≤ℝ b → c ≤ℝ d →
    overlapWidth a b c d ≡ overlapWidth c d a b
  overlapWidthSymmetric a b c d a≤b c≤d =
    orderCasesForPath a c (overlapWidth a b c d) (overlapWidth c d a b)
      (λ a≤c → orderCasesForPath b d
        (overlapWidth a b c d) (overlapWidth c d a b)
        (λ b≤d → orderCasesForPath c b
          (overlapWidth a b c d) (overlapWidth c d a b)
          (λ c≤b →
            cong₂ _-_ (clampAboveInterval a b d a≤b b≤d)
              (clampIntervalFix a b c a≤c c≤b)
            ∙ sym (cong₂ _-_ (clampIntervalFix c d b c≤b b≤d)
              (clampBelowInterval c d a a≤c)))
          (λ b≤c → overlapWidthBefore a b c d a≤b b≤c c≤d
            ∙ sym (overlapWidthAfter c d a b a≤b b≤c)))
        (λ d≤b →
          cong₂ _-_
            (clampIntervalFix a b d (≤ℝ-trans a c d a≤c c≤d) d≤b)
            (clampIntervalFix a b c a≤c (≤ℝ-trans c d b c≤d d≤b))
          ∙ sym (cong₂ _-_ (clampAboveInterval c d b c≤d d≤b)
            (clampBelowInterval c d a a≤c))))
      (λ c≤a → orderCasesForPath b d
        (overlapWidth a b c d) (overlapWidth c d a b)
        (λ b≤d →
          cong₂ _-_ (clampAboveInterval a b d a≤b b≤d)
            (clampBelowInterval a b c c≤a)
          ∙ sym (cong₂ _-_
            (clampIntervalFix c d b (≤ℝ-trans c a b c≤a a≤b) b≤d)
            (clampIntervalFix c d a c≤a (≤ℝ-trans a b d a≤b b≤d))))
        (λ d≤b → orderCasesForPath a d
          (overlapWidth a b c d) (overlapWidth c d a b)
          (λ a≤d →
            cong₂ _-_ (clampIntervalFix a b d a≤d d≤b)
              (clampBelowInterval a b c c≤a)
            ∙ sym (cong₂ _-_ (clampAboveInterval c d b c≤d d≤b)
              (clampIntervalFix c d a c≤a a≤d)))
          (λ d≤a → overlapWidthAfter a b c d c≤d d≤a
            ∙ sym (overlapWidthBefore c d a b c≤d d≤a a≤b))))

  overlappingTagsDistanceBound : ∀ a b c d x y →
    a ≤ℝ x → x ≤ℝ b → c ≤ℝ y → y ≤ℝ d →
    c ≤ℝ b → a ≤ℝ d →
    absℝ (x - y) ≤ℝ (b - a) + (d - c)
  overlappingTagsDistanceBound a b c d x y a≤x x≤b c≤y y≤d c≤b a≤d =
    subst (absℝ (x - y) ≤ℝ_) (sym cross)
      (absLeastUpperBound (x - y) ((b - c) + (d - a))
        (≤ℝ-trans (x - y) (b - c) ((b - c) + (d - a))
          (addPres≤ x b (- y) (- c) x≤b (negPres≤ c y c≤y))
          (subst (_≤ℝ (b - c) + (d - a)) (addIdR (b - c))
            (addPres≤L 0ℝ (d - a) (b - c) (nonnegativeSub a d a≤d))))
        (subst (_≤ℝ (b - c) + (d - a)) (sym (negSub x y))
          (≤ℝ-trans (y - x) (d - a) ((b - c) + (d - a))
            (addPres≤ y d (- x) (- a) y≤d (negPres≤ a x a≤x))
            (subst (_≤ℝ (b - c) + (d - a)) (addIdL (d - a))
              (addPres≤R 0ℝ (b - c) (d - a) (nonnegativeSub c b c≤b))))))
    where
    cross : (b - a) + (d - c) ≡ (b - c) + (d - a)
    cross = ℝRing.+ShufflePairs b (- a) d (- c)
      ∙ cong ((b + d) +_) (addComm (- a) (- c))
      ∙ sym (ℝRing.+ShufflePairs b (- c) d (- a))
