module Cubical.Analysis.Complex.FundamentalTheorem.Descent.KeyLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumStep
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumChain
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.StableTriple

-- The initial balanced radius is retained, together with a bounded offset
-- where the same index is a near-maximum at three consecutive radii.
StablePowerScale : ∀ {n} → Vec ℝ (suc n) → ℝ → ℝ → ℚ₊ → Type₀
StablePowerScale coefficients q target ε =
  Σ[ initial ∈ BalancedPowerScale coefficients Fin.toℕ target ε ]
    Stable.StableTriple C.tripleSteps (fst initial)
  where
  module C = FiniteNearMaxima (λ i → lookup i coefficients) q ε
  module Stable = StableNearMaxima (λ i → lookup i coefficients) q ε

finiteStablePowerScale : ∀ {n} (coefficients : Vec ℝ (suc n)) (q : ℝ) →
  (∀ i → 0ℝ ≤ℝ lookup i coefficients) → 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients →
  0ℝ <ℝ q → q ≤ℝ 1ℝ → (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) →
  q · rat (fst ε) ≤ℝ rat (fst (ε /2₊)) → ∥ StablePowerScale coefficients q target ε ∥₁
finiteStablePowerScale coefficients q nonnegative leading-positive q-positive q-small target target-positive ε error =
  PT.rec squash₁ fromBalanced
    (balanceFinitePowers coefficients Fin.toℕ nonnegative leading-positive target target-positive ε)
  where
  module C = FiniteNearMaxima (λ i → lookup i coefficients) q ε
  module Stable = StableNearMaxima (λ i → lookup i coefficients) q ε

  fromBalanced : BalancedPowerScale coefficients Fin.toℕ target ε →
    ∥ StablePowerScale coefficients q target ε ∥₁
  fromBalanced initial@(r , positive , k , selected , bounded) = PT.map
    (λ (chain , triple) → initial , Stable.extractStableTriple C.tripleSteps r k chain triple)
    (C.finiteNearMaximumTriple nonnegative q-positive q-small error
      r positive k λ i → subst (weightedPower (lookup i coefficients) (Fin.toℕ i) r <ℝ_)
        (cong (_+ rat (fst ε)) (sym selected)) (bounded i))
