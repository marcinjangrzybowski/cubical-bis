module Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation.Monad
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import
  Cubical.Tactics.CommRingSolver.Specialised.Rationals

UniformlyCauchySeries :
  ∀ {ℓ} →
  (X : Type ℓ) →
  (X → RealSequence) →
  Type ℓ
UniformlyCauchySeries X terms =
  Σ[ modulus ∈ (ℚ₊ → ℕ) ]
    (∀ ε x m n →
      modulus ε ℕ.≤ m →
      modulus ε ℕ.≤ n →
      partialSum (terms x) m
        ∼[ ε ]
      partialSum (terms x) n)

UniformlyAbsolutelyCauchySeries :
  ∀ {ℓ} →
  (X : Type ℓ) →
  (X → RealSequence) →
  Type ℓ
UniformlyAbsolutelyCauchySeries
  X terms =
    UniformlyCauchySeries
      X
      (λ x → absℝ ∘ terms x)

uniformlyCauchySeriesAt :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  ∀ x →
  IsCauchySeries (terms x)
uniformlyCauchySeriesAt
  X terms uniform x .fst =
    fst uniform
uniformlyCauchySeriesAt
  X terms uniform x .snd =
    λ ε m n modulus≤m modulus≤n →
      snd uniform
        ε x m n modulus≤m modulus≤n

uniformlyAbsolutelyCauchySeriesAt :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence) →
  UniformlyAbsolutelyCauchySeries
    X terms →
  ∀ x →
  IsAbsolutelyCauchySeries
    (terms x)
uniformlyAbsolutelyCauchySeriesAt
  X terms uniform =
    uniformlyCauchySeriesAt
      X
      (λ x → absℝ ∘ terms x)
      uniform

familyDominatedByCauchySeriesIsUniformlyCauchy :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence)
    bound →
  (∀ x n →
    absℝ (terms x n) ≤ℝ bound n) →
  IsCauchySeries bound →
  UniformlyCauchySeries X terms
familyDominatedByCauchySeriesIsUniformlyCauchy
  X terms bound dominates bound-cauchy
  .fst =
    fst bound-cauchy
familyDominatedByCauchySeriesIsUniformlyCauchy
  X terms bound dominates bound-cauchy
  .snd ε x m n modulus≤m modulus≤n =
    snd
      (dominatedCauchySeriesIsCauchy
        (terms x)
        bound
        (dominates x)
        bound-cauchy)
      ε m n modulus≤m modulus≤n

familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence)
    bound →
  (∀ x n →
    absℝ (terms x n) ≤ℝ bound n) →
  IsCauchySeries bound →
  UniformlyAbsolutelyCauchySeries
    X terms
familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
  X terms bound dominates bound-cauchy =
    familyDominatedByCauchySeriesIsUniformlyCauchy
      X
      (λ x → absℝ ∘ terms x)
      bound
      double-absolute-dominates
      bound-cauchy
  where
  double-absolute-dominates :
    ∀ x n →
    absℝ (absℝ (terms x n))
      ≤ℝ
    bound n
  double-absolute-dominates x n =
    subst
      (_≤ℝ bound n)
      (sym (absIdem (terms x n)))
      (dominates x n)

uniformAbsoluteCauchySeriesIsUniformCauchy :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence) →
  UniformlyAbsolutelyCauchySeries
    X terms →
  UniformlyCauchySeries X terms
uniformAbsoluteCauchySeriesIsUniformCauchy
  X terms absolute .fst =
    fst absolute
uniformAbsoluteCauchySeriesIsUniformCauchy
  X terms absolute
  .snd ε x m n modulus≤m modulus≤n =
    snd
      (absoluteCauchySeriesIsCauchy
        (terms x)
        (uniformlyAbsolutelyCauchySeriesAt
          X terms absolute x))
      ε m n modulus≤m modulus≤n

uniformlyCauchySeriesSummableAt :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  ∀ x →
  Summable (terms x)
uniformlyCauchySeriesSummableAt
  X terms uniform x =
    cauchySeriesIsSummable
      (terms x)
      (uniformlyCauchySeriesAt
        X terms uniform x)

uniformSeriesValue :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  X → ℝ
uniformSeriesValue
  X terms uniform x =
    seriesSum
      (terms x)
      (uniformlyCauchySeriesSummableAt
        X terms uniform x)

uniformPartialSumCloseToSeriesValue :
  ∀ {ℓ}
    (X : Type ℓ)
    (terms : X → RealSequence)
    (uniform :
      UniformlyCauchySeries X terms) →
  ∀ ε x n →
  fst uniform (ε /2₊) ℕ.≤ n →
  partialSum (terms x) n
    ∼[ ε ]
  uniformSeriesValue X terms uniform x
uniformPartialSumCloseToSeriesValue
  X terms uniform ε x n modulus≤n =
    PT.rec
      (isProp∼
        (partialSum (terms x) n)
        ε
        (uniformSeriesValue
          X terms uniform x))
      (λ (limit-index , eventually-close) →
        subst∼
          (partialSum (terms x) n)
          (uniformSeriesValue
            X terms uniform x)
          {ε = (ε /2₊) +₊ (ε /2₊)}
          {ε' = ε}
          (1/2∈ℚ./2+/2≡id
            (fst ε))
          (triangle∼
            (partialSum (terms x) n)
            (partialSum (terms x)
              (n +ℕ limit-index))
            (uniformSeriesValue
              X terms uniform x)
            (ε /2₊) (ε /2₊)
            (snd uniform
              (ε /2₊) x
              n (n +ℕ limit-index)
              modulus≤n
              (ℕ.≤-trans
                modulus≤n
                ℕ.≤SumLeft))
            (eventually-close
              (n +ℕ limit-index)
              ℕ.≤SumRight)))
      (seriesSumHasSum
        (terms x)
        (uniformlyCauchySeriesSummableAt
          X terms uniform x)
        (ε /2₊))

partialSumFamilyIsContinuous :
  ∀ {ℓ ℓ'}
    {X : Type ℓ}
    (source : PremetricStr ℓ' X)
    (terms : X → RealSequence) →
  (∀ n →
    isContinuous source
      (λ x → terms x n)
      (snd ℝPremetricSpace)) →
  ∀ n →
  isContinuous source
    (λ x → partialSum (terms x) n)
    (snd ℝPremetricSpace)
partialSumFamilyIsContinuous
  source terms term-continuous zero x
  .IsContinuousAt.pres≈ ε =
    return
      ( 1
      , λ _ _ → refl∼ 0 ε
      )
partialSumFamilyIsContinuous
  source terms term-continuous (suc n) =
    addOfContinuousIsContinuous
      source
      (λ x → partialSum (terms x) n)
      (λ x → terms x n)
      (partialSumFamilyIsContinuous
        source terms term-continuous n)
      (term-continuous n)

uniformSeriesValueIsContinuousFromPartialSums :
  ∀ {ℓ ℓ'}
    {X : Type ℓ}
    (source : PremetricStr ℓ' X)
    (terms : X → RealSequence)
    (uniform :
      UniformlyCauchySeries X terms) →
  (∀ n →
    isContinuous source
      (λ x → partialSum (terms x) n)
      (snd ℝPremetricSpace)) →
  isContinuous source
    (uniformSeriesValue X terms uniform)
    (snd ℝPremetricSpace)
uniformSeriesValueIsContinuousFromPartialSums
  source terms uniform partial-sum-continuous x
  .IsContinuousAt.pres≈ ε = do
    let
      index : ℕ
      index =
        fst uniform
          ((ε /4₊) /2₊)
    δ , partial-sum-near ←
      partial-sum-continuous index x
        .IsContinuousAt.pres≈
          (ε /2₊)
    return
      ( δ
      , λ y x∼y →
          subst∼
            (uniformSeriesValue
              _ terms uniform x)
            (uniformSeriesValue
              _ terms uniform y)
            {ε =
              (ε /4₊)
              +₊ ((ε /2₊) +₊ (ε /4₊))}
            {ε' = ε}
            ℚ!
            (triangle∼
              (uniformSeriesValue
                _ terms uniform x)
              (partialSum (terms x) index)
              (uniformSeriesValue
                _ terms uniform y)
              (ε /4₊)
              ((ε /2₊) +₊ (ε /4₊))
              (sym∼
                (partialSum (terms x) index)
                (uniformSeriesValue
                  _ terms uniform x)
                (ε /4₊)
                (uniformPartialSumCloseToSeriesValue
                  _ terms uniform
                  (ε /4₊) x index
                  ℕ.≤-refl))
              (triangle∼
                (partialSum (terms x) index)
                (partialSum (terms y) index)
                (uniformSeriesValue
                  _ terms uniform y)
                (ε /2₊) (ε /4₊)
                (partial-sum-near y x∼y)
                (uniformPartialSumCloseToSeriesValue
                  _ terms uniform
                  (ε /4₊) y index
                  ℕ.≤-refl)))
      )

uniformSeriesValueIsContinuous :
  ∀ {ℓ ℓ'}
    {X : Type ℓ}
    (source : PremetricStr ℓ' X)
    (terms : X → RealSequence)
    (uniform :
      UniformlyCauchySeries X terms) →
  (∀ n →
    isContinuous source
      (λ x → terms x n)
      (snd ℝPremetricSpace)) →
  isContinuous source
    (uniformSeriesValue X terms uniform)
    (snd ℝPremetricSpace)
uniformSeriesValueIsContinuous
  source terms uniform term-continuous =
    uniformSeriesValueIsContinuousFromPartialSums
      source terms uniform
      (partialSumFamilyIsContinuous
        source terms term-continuous)
