module Cubical.Analysis.Real.Series.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute

open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/4₊)


-- A single selected modulus controls all partial-sum sequences in the family.
-- This is stronger than pointwise native Cauchy data and is the appropriate
-- input for later uniform-limit and continuity theorems.
ChosenUniformlyCauchySeries : ∀ {ℓ} (A : Type ℓ) →
  (A → RealSequence) → Type ℓ
ChosenUniformlyCauchySeries A terms =
  Σ[ modulus ∈ (ℚ₊ → ℕ) ]
    (∀ point ε m n →
      modulus ε ℕ.≤ m → modulus ε ℕ.≤ n →
      partialSum (terms point) m ∼[ ε ]
      partialSum (terms point) n)


UniformlyCauchySeries : ∀ {ℓ} (A : Type ℓ) →
  (A → RealSequence) → Type ℓ
UniformlyCauchySeries A terms =
  ∥ ChosenUniformlyCauchySeries A terms ∥₁


isPropUniformlyCauchySeries : ∀ {ℓ} (A : Type ℓ) terms →
  isProp (UniformlyCauchySeries A terms)
isPropUniformlyCauchySeries A terms = squash₁


UniformHasSum : ∀ {ℓ} {A : Type ℓ} →
  (A → RealSequence) → (A → ℝ) → Type ℓ
UniformHasSum terms value =
  ∀ ε →
  ∥ Σ[ cutoff ∈ ℕ ]
      (∀ point n → cutoff ℕ.≤ n →
        partialSum (terms point) n ∼[ ε ] value point)
  ∥₁


isPropUniformHasSum : ∀ {ℓ} {A : Type ℓ}
  (terms : A → RealSequence) (value : A → ℝ) →
  isProp (UniformHasSum terms value)
isPropUniformHasSum terms value =
  isPropΠ λ _ → squash₁


UniformlySummableSeries : ∀ {ℓ} (A : Type ℓ) →
  (A → RealSequence) → Type ℓ
UniformlySummableSeries A terms =
  ∥ Σ[ value ∈ (A → ℝ) ] UniformHasSum terms value ∥₁


isPropUniformlySummableSeries : ∀ {ℓ} (A : Type ℓ)
  (terms : A → RealSequence) →
  isProp (UniformlySummableSeries A terms)
isPropUniformlySummableSeries A terms = squash₁


uniformlyCauchySeriesAt : ∀ {ℓ} {A : Type ℓ} {terms} →
  UniformlyCauchySeries A terms →
  ∀ point → IsCauchySeries (terms point)
uniformlyCauchySeriesAt uniform point =
  PT.map
    (λ where
      (modulus , close) →
        modulus , close point)
    uniform


uniformlyCauchySeriesSummableAt :
  ∀ {ℓ} {A : Type ℓ} {terms} →
  UniformlyCauchySeries A terms →
  ∀ point → Summable (terms point)
uniformlyCauchySeriesSummableAt {terms = terms} uniform point =
  cauchySeriesIsSummable (terms point)
    (uniformlyCauchySeriesAt uniform point)


uniformSeriesValue : ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence) →
  UniformlyCauchySeries A terms → A → ℝ
uniformSeriesValue terms uniform point =
  seriesSum (terms point)
    (uniformlyCauchySeriesSummableAt uniform point)


uniformHasSumAt : ∀ {ℓ} {A : Type ℓ}
  {terms : A → RealSequence} {value : A → ℝ} →
  UniformHasSum terms value →
  ∀ point → HasSum (terms point) (value point)
uniformHasSumAt uniform point ε =
  PT.map
    (λ where
      (cutoff , close) → cutoff , close point)
    (uniform ε)


chosenUniformSeriesLimit :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence) →
  ChosenUniformlyCauchySeries A terms → A → ℝ
chosenUniformSeriesLimit terms (modulus , close) point =
  lim (partialSum (terms point))
    ∣ modulus , close point ∣₁


chosenUniformlyCauchySeriesHasUniformSum :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence) →
  (chosen : ChosenUniformlyCauchySeries A terms) →
  UniformHasSum terms (chosenUniformSeriesLimit terms chosen)
chosenUniformlyCauchySeriesHasUniformSum
    terms chosen@(modulus , close) ε =
  ∣ modulus ((ε /4₊) /4₊)
  , (λ point n late →
      SP.close-lim-from-late
        (partialSum (terms point) n)
        (partialSum (terms point))
        (∣ modulus , close point ∣₁)
        modulus (close point) ε n late
        (refl∼ (partialSum (terms point) n)
          (((ε /4₊) /4₊) /4₊)))
  ∣₁


uniformlyCauchySeriesIsUniformlySummable :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence) →
  UniformlyCauchySeries A terms →
  UniformlySummableSeries A terms
uniformlyCauchySeriesIsUniformlySummable terms =
  PT.map λ chosen →
    chosenUniformSeriesLimit terms chosen
    , chosenUniformlyCauchySeriesHasUniformSum terms chosen


-- A point-independent native Cauchy majorant supplies one modulus for the
-- entire dominated family.
uniformlyDominatedSeriesIsUniformlyCauchy :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence) bound →
  (∀ point n → absℝ (terms point n) ≤ℝ bound n) →
  IsCauchySeries bound →
  UniformlyCauchySeries A terms
uniformlyDominatedSeriesIsUniformlyCauchy terms bound dominates =
  PT.map λ bound-cauchy →
    fst bound-cauchy
    , λ point ε m n modulus≤m modulus≤n →
      snd
        (dominatedChosenCauchySeriesIsChosenCauchy
          (terms point) bound (dominates point) bound-cauchy)
        ε m n modulus≤m modulus≤n
