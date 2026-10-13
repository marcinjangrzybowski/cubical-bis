module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Insert where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Base

insertPowerScale : ∀ {n} (a : ℝ) (tail : Vec ℝ n) (degrees : Fin (suc n) → ℕ) →
  (∀ i → 0ℝ ≤ℝ lookup i (a ∷ tail)) →
  (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) →
  BalancedPowerScale tail (λ i → degrees (suc i)) target ε →
  ∥ BalancedPowerScale (a ∷ tail) degrees target ε ∥₁
insertPowerScale a tail degrees nonnegative target target-positive ε
  (radius , radius-positive , index , selected , bounded) =
  PT.rec squash₁ (Sum.rec keep shrink)
    (dichotomyℝ target (weightedPower a (degrees zero) radius) (target + rat (fst ε))
      (slackAbove target ε))
  where
  keep : weightedPower a (degrees zero) radius <ℝ target + rat (fst ε) →
    ∥ BalancedPowerScale (a ∷ tail) degrees target ε ∥₁
  keep small = ∣ balancedScale {coefficients = a ∷ tail} {degrees = degrees}
    {target = target} {ε = ε} radius radius-positive (suc index) selected
    (λ { zero → small ; (suc i) → bounded i }) ∣₁

  shrink : target <ℝ weightedPower a (degrees zero) radius →
    ∥ BalancedPowerScale (a ∷ tail) degrees target ε ∥₁
  shrink large = ∣ balancedScale {coefficients = a ∷ tail} {degrees = degrees}
    {target = target} {ε = ε} W.radius W.radius-positive zero W.radius-equation
    (λ { zero → replaceBelow (weightedPower a (degrees zero) W.radius) target
           (target + rat (fst ε)) W.radius-equation (slackAbove target ε)
       ; (suc i) → ≤<ℝ-trans
           (weightedPower (lookup i tail) (degrees (suc i)) W.radius)
           (weightedPower (lookup i tail) (degrees (suc i)) radius)
           (target + rat (fst ε))
           (weightedPower-monotone (lookup i tail) (degrees (suc i)) W.radius radius
             (nonnegative (suc i)) (<ℝ-weaken 0ℝ W.radius W.radius-positive) decreases)
           (bounded i) }) ∣₁
    where
    a-positive : 0ℝ <ℝ a
    a-positive = positiveWeightedCoefficient a (degrees zero) radius (nonnegative zero)
      (<ℝ-trans 0ℝ target (weightedPower a (degrees zero) radius) target-positive large)

    module W = WeightedRoot (degrees zero) a target a-positive target-positive

    decreases : W.radius ≤ℝ radius
    decreases = W.radius-below radius (<ℝ-weaken 0ℝ radius radius-positive)
      (<ℝ-weaken target (weightedPower a (degrees zero) radius) large)
