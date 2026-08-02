module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.FiniteModification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ)
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Bounds
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.FiniteModification
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence

EventuallyCoefficientAbsBound :
  ℕ → ℚ₊ → RealSequence → Type
EventuallyCoefficientAbsBound
  cutoff C coefficients =
    ∀ n →
    cutoff ℕ.≤ n →
    absℝ (coefficients n)
      ≤ℝ rat (fst C)

removeCoefficientPrefix :
  ℕ → RealSequence → RealSequence
removeCoefficientPrefix
  cutoff coefficients n
  with ℕ.splitℕ-≤ cutoff n
... | inl _ =
  coefficients n
... | inr _ =
  0

removeCoefficientPrefixEventuallyEqual :
  ∀ cutoff coefficients →
  EventuallyEqualSeq
    (removeCoefficientPrefix
      cutoff coefficients)
    coefficients
removeCoefficientPrefixEventuallyEqual
  cutoff coefficients =
    cutoff , equal
  where
  equal : ∀ n →
    cutoff ℕ.≤ n →
    removeCoefficientPrefix
        cutoff coefficients n
      ≡
    coefficients n
  equal n cutoff≤n
    with ℕ.splitℕ-≤ cutoff n
  ... | inl _ =
    refl
  ... | inr n<cutoff =
    ⊥.rec
      (ℕ.<-asym n<cutoff cutoff≤n)

removeCoefficientPrefixBounded :
  ∀ cutoff C coefficients →
  EventuallyCoefficientAbsBound
    cutoff C coefficients →
  CoefficientAbsBound C
    (removeCoefficientPrefix
      cutoff coefficients)
removeCoefficientPrefixBounded
  cutoff C coefficients eventually-bounded n
  with ℕ.splitℕ-≤ cutoff n
... | inl cutoff≤n =
  eventually-bounded n cutoff≤n
... | inr _ =
  subst
    (_≤ℝ rat (fst C))
    (sym absZero)
    (positiveRationalNonnegative C)

removePrefixPowerSeriesEventuallyEqual :
  ∀ cutoff coefficients x →
  EventuallyEqualSeq
    (powerSeriesTerms
      (removeCoefficientPrefix
        cutoff coefficients)
      x)
    (powerSeriesTerms coefficients x)
removePrefixPowerSeriesEventuallyEqual
  cutoff coefficients x =
    cutoff
    , λ n cutoff≤n →
        cong
          (_· x ^ⁿ n)
          (snd
            (removeCoefficientPrefixEventuallyEqual
              cutoff coefficients)
            n cutoff≤n)

removePrefixAbsolutePowerSeriesEventuallyEqual :
  ∀ cutoff coefficients x →
  EventuallyEqualSeq
    (absℝ ∘
      powerSeriesTerms
        (removeCoefficientPrefix
          cutoff coefficients)
        x)
    (absℝ ∘
      powerSeriesTerms coefficients x)
removePrefixAbsolutePowerSeriesEventuallyEqual
  cutoff coefficients x =
    cutoff
    , λ n cutoff≤n →
        cong absℝ
          (snd
            (removePrefixPowerSeriesEventuallyEqual
              cutoff coefficients x)
            n cutoff≤n)

eventuallyBoundedPowerSeriesIsAbsolutelyCauchy :
  ∀ cutoff C coefficients x →
  EventuallyCoefficientAbsBound
    cutoff C coefficients →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
eventuallyBoundedPowerSeriesIsAbsolutelyCauchy
  cutoff C coefficients x
  eventually-bounded contraction =
    eventuallyEqualSeriesPresIsCauchy
      (absℝ ∘
        powerSeriesTerms
          bounded-coefficients x)
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (removePrefixAbsolutePowerSeriesEventuallyEqual
        cutoff coefficients x)
      bounded-power-series-absolute
  where
  bounded-coefficients : RealSequence
  bounded-coefficients =
    removeCoefficientPrefix
      cutoff coefficients

  bounded-power-series-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        bounded-coefficients x)
  bounded-power-series-absolute =
    powerSeriesIsAbsolutelyCauchy
      C bounded-coefficients x
      (removeCoefficientPrefixBounded
        cutoff C coefficients
        eventually-bounded)
      contraction

eventuallyBoundedPowerSeriesIsCauchy :
  ∀ cutoff C coefficients x →
  EventuallyCoefficientAbsBound
    cutoff C coefficients →
  RationalContractionBound x →
  IsCauchySeries
    (powerSeriesTerms coefficients x)
eventuallyBoundedPowerSeriesIsCauchy
  cutoff C coefficients x
  eventually-bounded contraction =
    absoluteCauchySeriesIsCauchy
      (powerSeriesTerms coefficients x)
      (eventuallyBoundedPowerSeriesIsAbsolutelyCauchy
        cutoff C coefficients x
        eventually-bounded contraction)

eventuallyBoundedPowerSeriesIsSummable :
  ∀ cutoff C coefficients x →
  EventuallyCoefficientAbsBound
    cutoff C coefficients →
  RationalContractionBound x →
  PowerSeriesSummableAt coefficients x
eventuallyBoundedPowerSeriesIsSummable
  cutoff C coefficients x
  eventually-bounded contraction =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms coefficients x)
      (eventuallyBoundedPowerSeriesIsAbsolutelyCauchy
        cutoff C coefficients x
        eventually-bounded contraction)
