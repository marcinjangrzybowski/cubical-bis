module Cubical.Analysis.Complex.FundamentalTheorem.Descent.SelectedTerm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
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
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteIndices
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Radii
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.PowerDecay
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.StableTriple
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.KeyLemma

-- The loss depends only on the number of nonconstant coefficients.
selectedTermFactor : ℕ → ℝ → ℝ
selectedTermFactor n q = powℝ (powℝ q (suc n)) (suc (twiceIndexBound n))

selectedTermFactor-positive : ∀ n q → 0ℝ <ℝ q → 0ℝ <ℝ selectedTermFactor n q
selectedTermFactor-positive n q positive = powPositive (powℝ q (suc n)) (suc (twiceIndexBound n))
  (powPositive q (suc n) positive)

selectedTermFactor<one : ∀ n q → 0ℝ <ℝ q → q <ℝ 1ℝ → selectedTermFactor n q <ℝ 1ℝ
selectedTermFactor<one n q positive below = ≤<ℝ-trans (selectedTermFactor n q) q 1ℝ
  (≤ℝ-trans (selectedTermFactor n q) δ q
    (powPositiveExponent≤Base δ (twiceIndexBound n)
      (<ℝ-weaken 0ℝ δ (powPositive q (suc n) positive))
      (powBelowOne q (suc n) nonnegative small))
    (powPositiveExponent≤Base q n nonnegative small)) below
  where
  δ = powℝ q (suc n)
  nonnegative = <ℝ-weaken 0ℝ q positive
  small = <ℝ-weaken q 1ℝ below

QuantitativeStablePowerScale : ∀ {n} → Vec ℝ (suc n) → ℝ → ℝ → ℚ₊ → Type₀
QuantitativeStablePowerScale {n} coefficients q target ε = Σ[ r ∈ ℝ ] (0ℝ <ℝ r) ×
  (Σ[ k ∈ Fin (suc n) ] Stable.ThreeNearMaxima r k ×
    (selectedTermFactor n q · target <ℝ term r k + rat (fst ε)) ×
    (term r k <ℝ target + rat (fst ε)))
  where
  module Stable = StableNearMaxima (λ i → lookup i coefficients) q ε
  term : ℝ → Fin (suc n) → ℝ
  term r k = weightedPower (lookup k coefficients) (Fin.toℕ k) (q · r)

quantitativeStablePowerScale : ∀ {n} (coefficients : Vec ℝ (suc n)) (q : ℝ) →
  (∀ i → 0ℝ ≤ℝ lookup i coefficients) → 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients →
  0ℝ <ℝ q → q ≤ℝ 1ℝ → (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) →
  q · rat (fst ε) ≤ℝ rat (fst (ε /2₊)) → ∥ QuantitativeStablePowerScale coefficients q target ε ∥₁
quantitativeStablePowerScale {n} coefficients q nonnegative leading-positive q-positive q-small target target-positive ε error =
  PT.map fromStable (finiteStablePowerScale coefficients q nonnegative leading-positive q-positive q-small target target-positive ε error)
  where
  fromStable : StablePowerScale coefficients q target ε → QuantitativeStablePowerScale coefficients q target ε
  fromStable ((initial , positive , first , equation , initial-bound) , offset , bounded , k , stable) =
    outer , outer-positive , k , stable , selected-lower , selected-upper
    where
    outer middle : ℝ
    outer = shrinkRadius q offset initial
    middle = q · outer

    outer-positive : 0ℝ <ℝ outer
    outer-positive = shrinkRadius-positive q offset initial q-positive positive

    middle-positive : 0ℝ <ℝ middle
    middle-positive = mulPositive q outer q-positive outer-positive

    weight : Fin (suc n) → ℝ
    weight i = weightedPower (lookup i coefficients) (Fin.toℕ i) middle

    selected-lower : selectedTermFactor n q · target <ℝ weight k + rat (fst ε)
    selected-lower = ≤<ℝ-trans (selectedTermFactor n q · target) (weight first) (weight k + rat (fst ε))
      (subst2 _≤ℝ_ (cong (selectedTermFactor n q ·_) equation)
        (cong (weightedPower (lookup first coefficients) (Fin.toℕ first)) (shrinkRadius-step q offset initial))
        (boundedShrinkWeightedLowerBound n (Fin.toℕ first) (suc offset) (suc (twiceIndexBound n))
          (lookup first coefficients) q initial (ℕ.pred-≤-pred (Fin.toℕ<n first))
          (ℕ.pred-≤-pred bounded) (nonnegative first) q-positive q-small positive))
      (fst (snd stable) first)

    selected-upper : weight k <ℝ target + rat (fst ε)
    selected-upper = ≤<ℝ-trans (weight k) (weightedPower (lookup k coefficients) (Fin.toℕ k) initial)
      (target + rat (fst ε))
      (weightedPower-monotone (lookup k coefficients) (Fin.toℕ k) middle initial (nonnegative k)
        (<ℝ-weaken 0ℝ middle middle-positive)
        (subst (_≤ℝ initial) (shrinkRadius-step q offset initial)
          (shrinkRadius≤initial q (suc offset) initial q-positive q-small positive)))
      (initial-bound k)
