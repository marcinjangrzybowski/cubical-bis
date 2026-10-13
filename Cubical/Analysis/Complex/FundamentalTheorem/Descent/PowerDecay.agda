module Cubical.Analysis.Complex.FundamentalTheorem.Descent.PowerDecay where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Rescale
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Radii

weightedPower-nonnegative : ∀ a i r → 0ℝ ≤ℝ a → 0ℝ ≤ℝ r → 0ℝ ≤ℝ weightedPower a i r
weightedPower-nonnegative a i r a-nonnegative r-nonnegative =
  isNonnegative→0≤ (weightedPower a i r)
    (mulPresIsNonnegative a (powℝ r (suc i)) (0≤→isNonnegative a a-nonnegative)
      (powPresIsNonnegative r (suc i) (0≤→isNonnegative r r-nonnegative)))

private
  oneStepLower : ∀ n i a q r → i ℕ.≤ n → 0ℝ ≤ℝ a → 0ℝ ≤ℝ q → q ≤ℝ 1ℝ → 0ℝ ≤ℝ r →
    powℝ q (suc n) · weightedPower a i r ≤ℝ weightedPower a i (q · r)
  oneStepLower n i a q r degree a-nonnegative q-nonnegative q-small r-nonnegative =
    subst (powℝ q (suc n) · weightedPower a i r ≤ℝ_) (sym (weightedPower-rescale a i q r))
      (mulPres≤R-0≤ (powℝ q (suc n)) (powℝ q (suc i)) (weightedPower a i r)
        (weightedPower-nonnegative a i r a-nonnegative r-nonnegative)
        (powAntitoneExponent q (suc i) (suc n) q-nonnegative q-small (ℕ.suc-≤-suc degree)))

-- No coefficient-dependent modulus is selected: each step loses at most
-- the same degree-dependent factor q^(suc n).
shrinkWeightedLowerBound : ∀ n i steps a q r → i ℕ.≤ n →
  0ℝ ≤ℝ a → 0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ <ℝ r →
  powℝ (powℝ q (suc n)) steps · weightedPower a i r ≤ℝ weightedPower a i (shrinkRadius q steps r)
shrinkWeightedLowerBound n i zero a q r degree a-nonnegative q-positive q-small r-positive =
  subst (_≤ℝ weightedPower a i r) (sym (mulIdL (weightedPower a i r))) (≤ℝ-refl (weightedPower a i r))
shrinkWeightedLowerBound n i (suc steps) a q r degree a-nonnegative q-positive q-small r-positive =
  ≤ℝ-trans (powℝ δ (suc steps) · weightedPower a i r)
    (powℝ δ steps · weightedPower a i (q · r)) (weightedPower a i (shrinkRadius q steps (q · r)))
    (subst (_≤ℝ powℝ δ steps · weightedPower a i (q · r))
      (mulAssoc (powℝ δ steps) δ (weightedPower a i r)
        ∙ cong (_· weightedPower a i r) (mulComm (powℝ δ steps) δ))
      (mulPres≤L (δ · weightedPower a i r) (weightedPower a i (q · r)) (powℝ δ steps)
        (0≤→isNonnegative (powℝ δ steps) (powNonnegative δ steps δ-nonnegative))
        (oneStepLower n i a q r degree a-nonnegative (<ℝ-weaken 0ℝ q q-positive) q-small
          (<ℝ-weaken 0ℝ r r-positive))))
    (shrinkWeightedLowerBound n i steps a q (q · r) degree a-nonnegative q-positive q-small
      (mulPositive q r q-positive r-positive))
  where
  δ = powℝ q (suc n)
  δ-nonnegative = powNonnegative q (suc n) (<ℝ-weaken 0ℝ q q-positive)

boundedShrinkWeightedLowerBound : ∀ n i steps bound a q r → i ℕ.≤ n → steps ℕ.≤ bound →
  0ℝ ≤ℝ a → 0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ <ℝ r →
  powℝ (powℝ q (suc n)) bound · weightedPower a i r ≤ℝ weightedPower a i (shrinkRadius q steps r)
boundedShrinkWeightedLowerBound n i steps bound a q r degree bounded a-nonnegative q-positive q-small r-positive =
  ≤ℝ-trans (powℝ δ bound · weightedPower a i r) (powℝ δ steps · weightedPower a i r)
    (weightedPower a i (shrinkRadius q steps r))
    (mulPres≤R-0≤ (powℝ δ bound) (powℝ δ steps) (weightedPower a i r)
      (weightedPower-nonnegative a i r a-nonnegative (<ℝ-weaken 0ℝ r r-positive))
      (powAntitoneExponent δ steps bound
        (powNonnegative q (suc n) q-nonnegative) (powBelowOne q (suc n) q-nonnegative q-small) bounded))
    (shrinkWeightedLowerBound n i steps a q r degree a-nonnegative q-positive q-small r-positive)
  where
  δ = powℝ q (suc n)
  q-nonnegative = <ℝ-weaken 0ℝ q q-positive
