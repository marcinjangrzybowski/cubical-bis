module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Singleton where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Base

private
  opaque
    scaleAtRadius : (a : ℝ) (degrees : Fin 1 → ℕ) (target : ℝ) (ε : ℚ₊)
      (r : ℝ) → 0ℝ <ℝ r → weightedPower a (degrees zero) r ≡ target →
      BalancedPowerScale (a ∷ []) degrees target ε
    scaleAtRadius a degrees target ε r positive equation =
      balancedScale {coefficients = a ∷ []} {degrees = degrees} {target = target} {ε = ε}
        r positive zero equation
        (λ { zero → replaceBelow (weightedPower a (degrees zero) r) target
               (target + rat (fst ε)) equation (slackAbove target ε)
           ; (suc ()) })

singletonPowerScale : (a : ℝ) (degrees : Fin 1 → ℕ) → 0ℝ <ℝ a →
  (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) → BalancedPowerScale (a ∷ []) degrees target ε
singletonPowerScale a degrees positive target target-positive ε =
  scaleAtRadius a degrees target ε W.radius W.radius-positive W.radius-equation
  where
  module W = WeightedRoot (degrees zero) a target positive target-positive
