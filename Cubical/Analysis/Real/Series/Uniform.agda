module Cubical.Analysis.Real.Series.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute

open PositiveRationals using (ℚ₊)
open PositiveRationals using (_+₊_; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; _/4₊)
open 1/2∈ℚ using (/2+/2≡id; /4+/4≡/2)

private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)


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


chosenUniformSeriesLimitIsUniformSeriesValue :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence)
    (chosen : ChosenUniformlyCauchySeries A terms) →
  chosenUniformSeriesLimit terms chosen ≡
  uniformSeriesValue terms ∣ chosen ∣₁
chosenUniformSeriesLimitIsUniformSeriesValue
    terms chosen@(modulus , close) =
  funExt λ point →
    canonicalLimit≡
      (partialSum (terms point))
      ∣ modulus , close point ∣₁
      (uniformSeriesValue terms ∣ chosen ∣₁ point)
      (seriesSumHasSum
        (terms point)
        (uniformlyCauchySeriesSummableAt ∣ chosen ∣₁ point))


uniformlyCauchySeriesHasUniformSum :
  ∀ {ℓ} {A : Type ℓ} (terms : A → RealSequence)
    (uniform : UniformlyCauchySeries A terms) →
  UniformHasSum terms (uniformSeriesValue terms uniform)
uniformlyCauchySeriesHasUniformSum {A = A} terms uniform =
  PT.rec
    (isPropUniformHasSum terms (uniformSeriesValue terms uniform))
    (λ chosen →
      subst
        (UniformHasSum terms)
        ( chosenUniformSeriesLimitIsUniformSeriesValue terms chosen
        ∙ cong (uniformSeriesValue terms)
            (isPropUniformlyCauchySeries A terms
              ∣ chosen ∣₁ uniform))
        (chosenUniformlyCauchySeriesHasUniformSum terms chosen))
    uniform


private
  quarterHalfQuarter : ∀ ε →
    fst ((ε /4₊) +₊ ((ε /2₊) +₊ (ε /4₊))) ≡ fst ε
  quarterHalfQuarter ε =
    ℚ.+Assoc
      (fst (ε /4₊)) (fst (ε /2₊)) (fst (ε /4₊))
    ∙ cong (ℚ._+ fst (ε /4₊))
        (ℚ.+Comm (fst (ε /4₊)) (fst (ε /2₊)))
    ∙ sym (ℚ.+Assoc
        (fst (ε /2₊)) (fst (ε /4₊)) (fst (ε /4₊)))
    ∙ cong (fst (ε /2₊) ℚ.+_)
        (/4+/4≡/2 (fst ε))
    ∙ /2+/2≡id (fst ε)


partialSumFamilyIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (terms : A → RealSequence) →
  (∀ n →
    isContinuous source
      (λ point → terms point n)
      (ℝPremetricSpace .snd)) →
  ∀ n →
  isContinuous source
    (λ point → partialSum (terms point) n)
    (ℝPremetricSpace .snd)
partialSumFamilyIsContinuous
    source terms term-continuous zero point
    .IsContinuousAt.pres≈ ε =
  ∣ ε , (λ _ _ → refl∼ 0ℝ ε) ∣₁
partialSumFamilyIsContinuous
    source terms term-continuous (suc n) =
  addOfContinuousIsContinuous
    source
    (λ point → partialSum (terms point) n)
    (λ point → terms point n)
    (partialSumFamilyIsContinuous
      source terms term-continuous n)
    (term-continuous n)


uniformSeriesValueIsContinuousFromPartialSums :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (terms : A → RealSequence)
    (uniform : UniformlyCauchySeries A terms) →
  (∀ n →
    isContinuous source
      (λ point → partialSum (terms point) n)
      (ℝPremetricSpace .snd)) →
  isContinuous source
    (uniformSeriesValue terms uniform)
    (ℝPremetricSpace .snd)
uniformSeriesValueIsContinuousFromPartialSums
  {A = A} source terms uniform partial-sum-continuous point
  .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ useUniformCutoff
    (uniformlyCauchySeriesHasUniformSum terms uniform (ε /4₊))
  where
  value : A → ℝ
  value = uniformSeriesValue terms uniform

  useUniformCutoff :
    (Σ[ cutoff ∈ ℕ ]
      (∀ y n → cutoff ℕ.≤ n →
        partialSum (terms y) n ∼[ ε /4₊ ] value y)) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_ source point δ y →
        value point ∼[ ε ] value y)
  useUniformCutoff (cutoff , close-to-value) =
    PT.map usePartialSumContinuity
      (partial-sum-continuous cutoff point
        .IsContinuousAt.pres≈ (ε /2₊))
    where
    usePartialSumContinuity :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_ source point δ y →
          partialSum (terms point) cutoff ∼[ ε /2₊ ]
          partialSum (terms y) cutoff)) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_ source point δ y →
          value point ∼[ ε ] value y)
    usePartialSumContinuity (δ , partial-close) =
      δ , λ y point≈y →
        Pℝ.subst≈ (value point) (value y)
          (quarterHalfQuarter ε)
          (triangle∼
            (value point)
            (partialSum (terms point) cutoff)
            (value y)
            (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (sym∼
              (partialSum (terms point) cutoff)
              (value point) (ε /4₊)
              (close-to-value point cutoff ℕ.≤-refl))
            (triangle∼
              (partialSum (terms point) cutoff)
              (partialSum (terms y) cutoff)
              (value y)
              (ε /2₊) (ε /4₊)
              (partial-close y point≈y)
              (close-to-value y cutoff ℕ.≤-refl)))


uniformSeriesValueIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (terms : A → RealSequence)
    (uniform : UniformlyCauchySeries A terms) →
  (∀ n →
    isContinuous source
      (λ point → terms point n)
      (ℝPremetricSpace .snd)) →
  isContinuous source
    (uniformSeriesValue terms uniform)
    (ℝPremetricSpace .snd)
uniformSeriesValueIsContinuous
    source terms uniform term-continuous =
  uniformSeriesValueIsContinuousFromPartialSums
    source terms uniform
    (partialSumFamilyIsContinuous
      source terms term-continuous)
