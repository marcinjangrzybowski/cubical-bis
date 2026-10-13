module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Base public using (BalancedPowerScale)
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Singleton
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Insert

-- The degree at i denotes exponent suc (degrees i). The final positive
-- coefficient starts the construction; all remaining coefficients are
-- inserted in a finite descending scan under propositional truncation.
balanceFinitePowers : ∀ {n} (coefficients : Vec ℝ (suc n)) (degrees : Fin (suc n) → ℕ) →
  (∀ i → 0ℝ ≤ℝ lookup i coefficients) → 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients →
  (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) → ∥ BalancedPowerScale coefficients degrees target ε ∥₁
balanceFinitePowers (a ∷ []) degrees nonnegative positive target target-positive ε =
  ∣ singletonPowerScale a degrees positive target target-positive ε ∣₁
balanceFinitePowers (a ∷ b ∷ tail) degrees nonnegative positive target target-positive ε =
  PT.rec squash₁ (insertPowerScale a (b ∷ tail) degrees nonnegative target target-positive ε)
    (balanceFinitePowers (b ∷ tail) (λ i → degrees (suc i))
      (λ i → nonnegative (suc i)) positive target target-positive ε)
