module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List
  using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base

polynomialCoefficientSequence :
  List ℝ → RealSequence
polynomialCoefficientSequence [] n =
  0
polynomialCoefficientSequence
  (coefficient ∷ coefficients) zero =
    coefficient
polynomialCoefficientSequence
  (coefficient ∷ coefficients) (suc n) =
    polynomialCoefficientSequence coefficients n

private
  commuteNestedProduct :
    ∀ (a b c : ℝ) →
    a · (b · c) ≡ b · (a · c)
  commuteNestedProduct a b c =
    sym (mulAssoc a b c)
    ∙ cong (_· c) (mulComm a b)
    ∙ mulAssoc b a c

polynomialCoefficientPartialSumStep :
  ∀ coefficient coefficients x n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence
          (coefficient ∷ coefficients))
        x)
      (suc n)
    ≡
  coefficient
    + x · partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence
            coefficients)
          x)
        n
polynomialCoefficientPartialSumStep
  coefficient coefficients x zero =
    addIdL (coefficient · 1)
    ∙ mulIdR coefficient
    ∙ sym (addIdR coefficient)
    ∙ cong (coefficient +_)
        (sym (mulZeroR x))
polynomialCoefficientPartialSumStep
  coefficient coefficients x (suc n) =
    cong
      (_+ polynomialCoefficientSequence
          coefficients n · x ^ⁿ suc n)
      (polynomialCoefficientPartialSumStep
        coefficient coefficients x n)
    ∙ cong
        ((coefficient + x · tail-sum) +_)
        (commuteNestedProduct
          (polynomialCoefficientSequence
            coefficients n)
          x (x ^ⁿ n))
    ∙ sym
        (addAssoc
          coefficient
          (x · tail-sum)
          (x · tail-term))
    ∙ cong
        (coefficient +_)
        (sym
          (mulDistR
            x tail-sum tail-term))
  where
  tail-sum : ℝ
  tail-sum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence
          coefficients)
        x)
      n

  tail-term : ℝ
  tail-term =
    polynomialCoefficientSequence
      coefficients n · x ^ⁿ n

evaluatePolynomialAsFinitePowerSeries :
  ∀ coefficients x →
  evaluatePolynomial coefficients x
    ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence
        coefficients)
      x)
    (length coefficients)
evaluatePolynomialAsFinitePowerSeries
  [] x =
    refl
evaluatePolynomialAsFinitePowerSeries
  (coefficient ∷ coefficients) x =
    cong
      (λ value → coefficient + x · value)
      (evaluatePolynomialAsFinitePowerSeries
        coefficients x)
    ∙ sym
        (polynomialCoefficientPartialSumStep
          coefficient coefficients x
          (length coefficients))

polynomialCoefficientSequence-zeroAfterLength :
  ∀ coefficients n →
  polynomialCoefficientSequence coefficients
      (length coefficients +ℕ n)
    ≡
  0
polynomialCoefficientSequence-zeroAfterLength
  [] n =
    refl
polynomialCoefficientSequence-zeroAfterLength
  (coefficient ∷ coefficients) n =
    polynomialCoefficientSequence-zeroAfterLength
      coefficients n

polynomialPowerSeriesTerm-zeroAfterLength :
  ∀ coefficients x n →
  powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x
      (n +ℕ length coefficients)
    ≡
  0
polynomialPowerSeriesTerm-zeroAfterLength
  coefficients x n =
    cong
      (_· x ^ⁿ (n +ℕ length coefficients))
      (subst
        (λ index →
          polynomialCoefficientSequence
            coefficients index ≡ 0)
        (Nat.+-comm
          (length coefficients) n)
        (polynomialCoefficientSequence-zeroAfterLength
          coefficients n))
    ∙ mulZeroL
        (x ^ⁿ (n +ℕ length coefficients))

polynomialPowerSeriesPartialSumStable :
  ∀ coefficients x n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients)
        x)
      (n +ℕ length coefficients)
    ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x)
    (length coefficients)
polynomialPowerSeriesPartialSumStable
  coefficients x zero =
    refl
polynomialPowerSeriesPartialSumStable
  coefficients x (suc n) =
    cong
      (_+ powerSeriesTerms
          (polynomialCoefficientSequence coefficients)
          x
          (n +ℕ length coefficients))
      (polynomialPowerSeriesPartialSumStable
        coefficients x n)
    ∙ cong
        (partialSum
          (powerSeriesTerms
            (polynomialCoefficientSequence coefficients)
            x)
          (length coefficients) +_)
        (polynomialPowerSeriesTerm-zeroAfterLength
          coefficients x n)
    ∙ addIdR
        (partialSum
          (powerSeriesTerms
            (polynomialCoefficientSequence coefficients)
            x)
          (length coefficients))

polynomialPowerSeriesPartialSumStableAbove :
  ∀ coefficients x n →
  length coefficients ℕ.≤ n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients)
        x)
      n
    ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x)
    (length coefficients)
polynomialPowerSeriesPartialSumStableAbove
  coefficients x n (count , count+length≡n) =
    subst
      (λ index →
        partialSum terms index
          ≡ partialSum terms
              (length coefficients))
      count+length≡n
      (polynomialPowerSeriesPartialSumStable
        coefficients x count)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x

polynomialPowerSeriesHasFiniteSum :
  ∀ coefficients x →
  HasSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x)
    (partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients)
        x)
      (length coefficients))
polynomialPowerSeriesHasFiniteSum
  coefficients x ε =
    return
      ( length coefficients
      , λ k (count , count+length≡k) →
          subst
            (λ index →
              partialSum terms index
                ∼[ ε ]
              partialSum terms
                (length coefficients))
            count+length≡k
            (subst
              (_∼[ ε ]
                partialSum terms
                  (length coefficients))
              (sym
                (polynomialPowerSeriesPartialSumStable
                  coefficients x count))
              (refl∼
                (partialSum terms
                  (length coefficients))
                ε))
      )
  where
  terms : RealSequence
  terms =
    powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x

polynomialPowerSeriesSummable :
  ∀ coefficients x →
  PowerSeriesSummableAt
    (polynomialCoefficientSequence coefficients)
    x
polynomialPowerSeriesSummable
  coefficients x =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients)
        x)
      (length coefficients)
    , polynomialPowerSeriesHasFiniteSum
        coefficients x

polynomialPowerSeriesValue :
  ∀ coefficients x →
  (summable :
    PowerSeriesSummableAt
      (polynomialCoefficientSequence coefficients)
      x) →
  powerSeriesValue
      (polynomialCoefficientSequence coefficients)
      x summable
    ≡
  evaluatePolynomial coefficients x
polynomialPowerSeriesValue
  coefficients x summable =
    seriesSumIndependent
      terms summable
      (polynomialPowerSeriesSummable
        coefficients x)
    ∙ sym
        (evaluatePolynomialAsFinitePowerSeries
          coefficients x)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms
      (polynomialCoefficientSequence coefficients)
      x
