module Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumStep where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.PrefixMaximum
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Rescale

PowerNearMaximum : ∀ {n} → (Fin n → ℝ) → ℝ → ℚ₊ → Fin n → Type₀
PowerNearMaximum coefficients r ε k = ∀ i →
  weightedPower (coefficients i) (Fin.toℕ i) r <ℝ
    weightedPower (coefficients k) (Fin.toℕ k) r + rat (fst ε)

private
  opaque
    weakenHalfComparison : ∀ x y ε → x <ℝ y + rat (fst (ε /2₊)) → x <ℝ y + rat (fst ε)
    weakenHalfComparison x y ε below = <ℝ-trans x (y + rat (fst (ε /2₊))) (y + rat (fst ε)) below
      (<ℝ-addL (rat (fst (ε /2₊))) (rat (fst ε)) y
        (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))

    chainHalfComparisons : ∀ x y z ε → x <ℝ y + rat (fst (ε /2₊)) →
      y <ℝ z + rat (fst (ε /2₊)) → x <ℝ z + rat (fst ε)
    chainHalfComparisons x y z ε first second =
      subst (x <ℝ_)
        (sym (addAssoc z δ δ) ∙ cong (z +_)
          (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε))))
        (<ℝ-trans x (y + δ) ((z + δ) + δ) first (<ℝ-addR y (z + δ) δ second))
      where
      δ : ℝ
      δ = rat (fst (ε /2₊))

-- A finite prefix maximum at the next radius preserves the global
-- approximation invariant and never increases the selected index.
nextPowerNearMaximum : ∀ {n} (coefficients : Fin n → ℝ) q r ε k →
  (∀ i → 0ℝ ≤ℝ coefficients i) → 0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ ≤ℝ r →
  q · rat (fst ε) ≤ℝ rat (fst (ε /2₊)) → PowerNearMaximum coefficients r ε k →
  ∥ Σ[ j ∈ Fin n ] (Fin.toℕ j ℕ.≤ Fin.toℕ k) × PowerNearMaximum coefficients (q · r) ε j ∥₁
nextPowerNearMaximum coefficients q r ε k nonnegative q-positive q-small r-nonnegative error old-maximum =
  PT.map fromPrefix (prefixApproximateMaximum new k (ε /2₊))
  where
  new : _ → ℝ
  new i = weightedPower (coefficients i) (Fin.toℕ i) (q · r)

  fromPrefix : _ → _
  fromPrefix (j , decreases , maximum) = j , decreases , λ i →
    Sum.rec
      (λ inside → weakenHalfComparison (new i) (new j) ε (maximum i inside))
      (λ outside → chainHalfComparisons (new i) (new k) (new j) ε
        (rescaledNearMaximum (coefficients i) (coefficients k) (Fin.toℕ i) (Fin.toℕ k)
          q r (rat (fst ε)) (rat (fst (ε /2₊))) (nonnegative k) (ℕ.<-weaken outside)
          q-positive q-small r-nonnegative (<ℝ-weaken 0ℝ (rat (fst ε)) (<ℚ→<ℝ 0 (fst ε) (snd ε)))
          error (old-maximum i))
        (maximum k ℕ.≤-refl))
      (ℕ.splitℕ-≤ (Fin.toℕ i) (Fin.toℕ k))
