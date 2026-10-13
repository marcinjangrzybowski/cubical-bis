module Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Continuity
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Roots.Positive

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

weightedPower : ℝ → ℕ → ℝ → ℝ
weightedPower a n r = a · powℝ r (suc n)

weightedPower-monotone : ∀ a n x y → 0ℝ ≤ℝ a → 0ℝ ≤ℝ x → x ≤ℝ y →
  weightedPower a n x ≤ℝ weightedPower a n y
weightedPower-monotone a n x y nonnegative xp ordered =
  mulPres≤L (powℝ x (suc n)) (powℝ y (suc n)) a (0≤→isNonnegative a nonnegative)
    (powMono (suc n) xp ordered)

weightedPower-strictlyIncreasing : ∀ a n x y → 0ℝ <ℝ a → 0ℝ ≤ℝ x → x <ℝ y →
  weightedPower a n x <ℝ weightedPower a n y
weightedPower-strictlyIncreasing a n x y positive xp ordered =
  mulPres<PosL (powℝ x (suc n)) (powℝ y (suc n)) a positive
    (powStrictMonoNonnegative n x y xp ordered)

positiveWeightedCoefficient : ∀ a n r → 0ℝ ≤ℝ a → 0ℝ <ℝ weightedPower a n r → 0ℝ <ℝ a
positiveWeightedCoefficient a n r nonnegative positive =
  continuousReflectsStrictOnOrderedInputs (_· powℝ r (suc n)) (mul-isContinuous₁ (powℝ r (suc n)))
    0ℝ a nonnegative
    (subst (_<ℝ weightedPower a n r) (sym (R.0LeftAnnihilates (powℝ r (suc n)))) positive)

module WeightedRoot (n : ℕ) (a t : ℝ) (a-positive : 0ℝ <ℝ a) (t-positive : 0ℝ <ℝ t) where
  private
    reciprocal : ℝ
    reciprocal = positiveReciprocal a a-positive

    quotient-positive : 0ℝ <ℝ t · reciprocal
    quotient-positive = mulPositive t reciprocal t-positive (positiveReciprocalPositive a a-positive)

    undoDivision : a · (t · reciprocal) ≡ t
    undoDivision = mulAssoc a t reciprocal ∙ cong (_· reciprocal) (mulComm a t)
      ∙ sym (mulAssoc t a reciprocal)
      ∙ cong (t ·_) (positiveReciprocalLaw a a-positive) ∙ mulIdR t

  opaque
    radius : ℝ
    radius = positiveRootℝ n (t · reciprocal) quotient-positive

    radius-positive : 0ℝ <ℝ radius
    radius-positive = positiveRootℝ-positive n (t · reciprocal) quotient-positive

    radius-equation : weightedPower a n radius ≡ t
    radius-equation = cong (a ·_) (positiveRootℝ-power n (t · reciprocal) quotient-positive)
      ∙ undoDivision

  radius-below : ∀ r → 0ℝ ≤ℝ r → t ≤ℝ weightedPower a n r → radius ≤ℝ r
  radius-below r nonnegative bounded = notGreater→≤ℝ radius r λ greater →
    ≤ℝ→≯ t (weightedPower a n r) bounded
      (subst (weightedPower a n r <ℝ_) radius-equation
        (weightedPower-strictlyIncreasing a n r radius a-positive nonnegative greater))
