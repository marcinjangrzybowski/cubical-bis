module Cubical.Analysis.Real.Series.PowerSeries.Polynomial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as NatOrder

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  commuteNestedProduct : ∀ (a b c : ℝ) →
    a · (b · c) ≡ b · (a · c)
  commuteNestedProduct a b c =
    mulAssoc a b c
    ∙ cong (_· c) (mulComm a b)
    ∙ sym (mulAssoc b a c)


polynomialCoefficientSequence : List ℝ → RealSequence
polynomialCoefficientSequence [] n = 0ℝ
polynomialCoefficientSequence (coefficient ∷ coefficients) zero =
  coefficient
polynomialCoefficientSequence (coefficient ∷ coefficients) (suc n) =
  polynomialCoefficientSequence coefficients n


polynomialCoefficientPartialSumStep :
  ∀ coefficient coefficients x n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence
          (coefficient ∷ coefficients)) x)
      (suc n)
    ≡
  coefficient
    + x · partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence coefficients) x)
        n
polynomialCoefficientPartialSumStep
    coefficient coefficients x zero =
  addIdL (coefficient · powℝ x zero)
  ∙ mulIdR coefficient
  ∙ sym (addIdR coefficient)
  ∙ cong (coefficient +_)
      (sym (ℝRing.0RightAnnihilates x))
polynomialCoefficientPartialSumStep
    coefficient coefficients x (suc n) =
  cong
    (_+ polynomialCoefficientSequence coefficients n
      · powℝ x (suc n))
    (polynomialCoefficientPartialSumStep
      coefficient coefficients x n)
  ∙ cong
      ((coefficient + x · tailSum) +_)
      (commuteNestedProduct
        (polynomialCoefficientSequence coefficients n)
        x (powℝ x n))
  ∙ sym
      (addAssoc coefficient
        (x · tailSum) (x · tailTerm))
  ∙ cong (coefficient +_)
      (sym (mulDistR x tailSum tailTerm))
  where
  tailSum : ℝ
  tailSum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x)
      n

  tailTerm : ℝ
  tailTerm =
    polynomialCoefficientSequence coefficients n
      · powℝ x n


evaluatePolynomialAsFinitePowerSeries : ∀ coefficients x →
  evaluatePolynomial coefficients x ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (length coefficients)
evaluatePolynomialAsFinitePowerSeries [] x = refl
evaluatePolynomialAsFinitePowerSeries
    (coefficient ∷ coefficients) x =
  cong (λ value → coefficient + x · value)
    (evaluatePolynomialAsFinitePowerSeries coefficients x)
  ∙ sym
      (polynomialCoefficientPartialSumStep
        coefficient coefficients x (length coefficients))


polynomialCoefficientSequence-zeroAfterLength :
  ∀ coefficients n →
  polynomialCoefficientSequence coefficients
      (length coefficients +ℕ n)
    ≡ 0ℝ
polynomialCoefficientSequence-zeroAfterLength [] n = refl
polynomialCoefficientSequence-zeroAfterLength
    (coefficient ∷ coefficients) n =
  polynomialCoefficientSequence-zeroAfterLength coefficients n


polynomialPowerSeriesTerm-zeroAfterLength :
  ∀ coefficients x n →
  powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x
      (n +ℕ length coefficients)
    ≡ 0ℝ
polynomialPowerSeriesTerm-zeroAfterLength coefficients x n =
  cong
    (λ coefficient →
      coefficient · powℝ x (n +ℕ length coefficients))
    (subst
      (λ index →
        polynomialCoefficientSequence coefficients index ≡ 0ℝ)
      (Nat.+-comm (length coefficients) n)
      (polynomialCoefficientSequence-zeroAfterLength
        coefficients n))
  ∙ ℝRing.0LeftAnnihilates
      (powℝ x (n +ℕ length coefficients))


polynomialPowerSeriesPartialSumStable :
  ∀ coefficients x n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x)
      (n +ℕ length coefficients)
    ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (length coefficients)
polynomialPowerSeriesPartialSumStable coefficients x zero = refl
polynomialPowerSeriesPartialSumStable coefficients x (suc n) =
  cong
    (_+ powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x
      (n +ℕ length coefficients))
    (polynomialPowerSeriesPartialSumStable coefficients x n)
  ∙ cong
      (partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence coefficients) x)
        (length coefficients) +_)
      (polynomialPowerSeriesTerm-zeroAfterLength
        coefficients x n)
  ∙ addIdR
      (partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence coefficients) x)
        (length coefficients))


polynomialPowerSeriesPartialSumStableAbove :
  ∀ coefficients x n →
  length coefficients NatOrder.≤ n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x) n
    ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (length coefficients)
polynomialPowerSeriesPartialSumStableAbove
    coefficients x n (count , count+length≡n) =
  subst
    (λ index →
      partialSum terms index ≡
      partialSum terms (length coefficients))
    count+length≡n
    (polynomialPowerSeriesPartialSumStable
      coefficients x count)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x


polynomialPowerSeriesChosenCauchy : ∀ coefficients x →
  ChosenIsCauchySequence
    (partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x))
polynomialPowerSeriesChosenCauchy coefficients x .fst ε =
  length coefficients
polynomialPowerSeriesChosenCauchy coefficients x .snd
    ε m n length≤m length≤n =
  subst2 (_∼[ ε ]_)
    (sym (polynomialPowerSeriesPartialSumStableAbove
      coefficients x m length≤m))
    (sym (polynomialPowerSeriesPartialSumStableAbove
      coefficients x n length≤n))
    (refl∼ stableSum ε)
  where
  stableSum : ℝ
  stableSum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x)
      (length coefficients)


polynomialPowerSeriesIsCauchy : ∀ coefficients x →
  IsCauchySeries
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
polynomialPowerSeriesIsCauchy coefficients x =
  ∣ polynomialPowerSeriesChosenCauchy coefficients x ∣₁


polynomialPowerSeriesHasFiniteSum : ∀ coefficients x →
  HasSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x)
      (length coefficients))
polynomialPowerSeriesHasFiniteSum coefficients x =
  eventuallyEqualPresIsLimitSequence
    ∣ length coefficients
    , (λ n length≤n →
        sym (polynomialPowerSeriesPartialSumStableAbove
          coefficients x n length≤n))
    ∣₁
    (constantIsLimitSequence stableSum)
  where
  stableSum : ℝ
  stableSum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x)
      (length coefficients)


polynomialPowerSeriesSummable : ∀ coefficients x →
  PowerSeriesSummableAt
    (polynomialCoefficientSequence coefficients) x
polynomialPowerSeriesSummable coefficients x =
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (length coefficients)
  , polynomialPowerSeriesHasFiniteSum coefficients x


polynomialPowerSeriesValue : ∀ coefficients x →
  (summable : PowerSeriesSummableAt
    (polynomialCoefficientSequence coefficients) x) →
  powerSeriesValue
      (polynomialCoefficientSequence coefficients) x summable
    ≡
  evaluatePolynomial coefficients x
polynomialPowerSeriesValue coefficients x summable =
  seriesSumIndependent
    terms summable (polynomialPowerSeriesSummable coefficients x)
  ∙ sym (evaluatePolynomialAsFinitePowerSeries coefficients x)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x
