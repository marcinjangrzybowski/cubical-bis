module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Dominance where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.StableTriple
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SelectedTerm
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorAllowance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.OffDiagonal

module _ {n} (coefficients : Fin (suc n) → ℝ) (q : ℝ) (positive : 0ℝ <ℝ q) (ε : ℚ₊) where
  private
    module Stable = StableNearMaxima coefficients q ε
    module Error = PowerErrorAllowance n q positive (rat (fst ε))
    ε-nonnegative = <ℝ-weaken 0ℝ (rat (fst ε)) (<ℚ→<ℝ 0 (fst ε) (snd ε))

  stableTriple-offDiagonal : (∀ i → 0ℝ ≤ℝ coefficients i) → q ≤ℝ 1ℝ →
    ∀ r k → 0ℝ <ℝ r → Stable.ThreeNearMaxima r k → ∀ i → ¬ (i ≡ k) →
    weightedPower (coefficients i) (Fin.toℕ i) (q · r) <ℝ
      q · weightedPower (coefficients k) (Fin.toℕ k) (q · r) + Error.allowance
  stableTriple-offDiagonal nonnegative small r k r-positive (outer , middle , inner) i different =
    fromOrder (Fin.toℕ i ℕ.≟ Fin.toℕ k)
    where
    fromOrder : ℕ.Trichotomy (Fin.toℕ i) (Fin.toℕ k) →
      weightedPower (coefficients i) (Fin.toℕ i) (q · r) <ℝ
        q · weightedPower (coefficients k) (Fin.toℕ k) (q · r) + Error.allowance
    fromOrder (ℕ.lt less) = lowerIndexBound (coefficients i) (coefficients k) (Fin.toℕ i) (Fin.toℕ k)
      q (q · r) (rat (fst ε)) Error.allowance less (nonnegative k) positive small
      (<ℝ-weaken 0ℝ (q · r) (mulPositive q r positive r-positive))
      (Error.allowance-scaled (Fin.toℕ i) (ℕ.pred-≤-pred (Fin.toℕ<n i)) small ε-nonnegative) (inner i)
    fromOrder (ℕ.eq equal) = ⊥.rec (different (Fin.inj-toℕ equal))
    fromOrder (ℕ.gt greater) = higherIndexBound (coefficients i) (coefficients k) (Fin.toℕ i) (Fin.toℕ k)
      q r (rat (fst ε)) Error.allowance greater (nonnegative k) positive small (<ℝ-weaken 0ℝ r r-positive)
      ε-nonnegative (Error.allowance-expands small ε-nonnegative) (outer i)

degreeErrorAllowance : ℕ → ℚ₊ → ℝ
degreeErrorAllowance n ε = PowerErrorAllowance.allowance n (degreeShrink n) (degreeShrink-positive n) (rat (fst ε))

-- r is now the middle radius, ready for the angular cancellation step.
DominantPowerScale : ∀ {n} → Vec ℝ (suc n) → ℝ → ℚ₊ → Type₀
DominantPowerScale {n} coefficients target ε = Σ[ r ∈ ℝ ] (0ℝ <ℝ r) ×
  (Σ[ k ∈ Fin (suc n) ]
    (selectedTermFactor n (degreeShrink n) · target <ℝ weight r k + rat (fst ε)) ×
    (weight r k <ℝ target + rat (fst ε)) ×
    (∀ i → ¬ (i ≡ k) → weight r i <ℝ degreeShrink n · weight r k + degreeErrorAllowance n ε))
  where
  weight : ℝ → Fin (suc n) → ℝ
  weight r i = weightedPower (lookup i coefficients) (Fin.toℕ i) r

finiteDominantPowerScale : ∀ {n} (coefficients : Vec ℝ (suc n)) →
  (∀ i → 0ℝ ≤ℝ lookup i coefficients) → 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients →
  (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) → ∥ DominantPowerScale coefficients target ε ∥₁
finiteDominantPowerScale {n} coefficients nonnegative leading-positive target target-positive ε =
  PT.map fromSelected
    (quantitativeStablePowerScale coefficients (degreeShrink n) nonnegative leading-positive
      (degreeShrink-positive n) (degreeShrink≤one n) target target-positive ε (degreeShrink-error n ε))
  where
  fromSelected : QuantitativeStablePowerScale coefficients (degreeShrink n) target ε →
    DominantPowerScale coefficients target ε
  fromSelected (r , positive , k , stable , selected-lower , selected-upper) =
    degreeShrink n · r , mulPositive (degreeShrink n) r (degreeShrink-positive n) positive ,
      k , selected-lower , selected-upper ,
      stableTriple-offDiagonal (λ i → lookup i coefficients) (degreeShrink n) (degreeShrink-positive n) ε
        nonnegative (degreeShrink≤one n) r k positive stable
