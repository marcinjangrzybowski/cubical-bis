module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Polynomial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base


polynomialCoefficientSequence :
  List Real.ℝ → RealSequence
polynomialCoefficientSequence [] n = zeroℝ
polynomialCoefficientSequence (coefficient ∷ coefficients) zero =
  coefficient
polynomialCoefficientSequence (coefficient ∷ coefficients) (suc n) =
  polynomialCoefficientSequence coefficients n


private
  commuteNestedProduct : ∀ (a b c : Real.ℝ) →
    a Mul.· (b Mul.· c) ≡ b Mul.· (a Mul.· c)
  commuteNestedProduct a b c =
    mul-assoc a b c
    ∙ cong (Mul._· c) (mul-comm a b)
    ∙ sym (mul-assoc b a c)


polynomialCoefficientPartialSumStep :
  ∀ coefficient coefficients x n →
  partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence
          (coefficient ∷ coefficients)) x)
      (suc n)
    ≡
  coefficient Add.+
    x Mul.· partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x) n
polynomialCoefficientPartialSumStep
    coefficient coefficients x zero =
  add-zero-left (coefficient Mul.· (x ^ⁿ zero))
  ∙ mul-one-right coefficient
  ∙ sym (add-zero-right coefficient)
  ∙ cong (coefficient Add.+_)
      (sym (mul-zero-right x))
polynomialCoefficientPartialSumStep
    coefficient coefficients x (suc n) =
  cong
    (Add._+ (polynomialCoefficientSequence coefficients n Mul.·
      x ^ⁿ suc n))
    (polynomialCoefficientPartialSumStep
      coefficient coefficients x n)
  ∙ cong
      ((coefficient Add.+ x Mul.· tail-sum) Add.+_)
      (commuteNestedProduct
        (polynomialCoefficientSequence coefficients n)
        x (x ^ⁿ n))
  ∙ sym
      (add-assoc coefficient
        (x Mul.· tail-sum)
        (x Mul.· tail-term))
  ∙ cong (coefficient Add.+_)
      (sym (mul-distrib-over-add-right x tail-sum tail-term))
  where
  tail-sum : Real.ℝ
  tail-sum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x) n

  tail-term : Real.ℝ
  tail-term =
    polynomialCoefficientSequence coefficients n Mul.· x ^ⁿ n


evaluatePolynomialAsFinitePowerSeries : ∀ coefficients x →
  evaluatePolynomial coefficients x ≡
  partialSum
    (powerSeriesTerms
      (polynomialCoefficientSequence coefficients) x)
    (length coefficients)
evaluatePolynomialAsFinitePowerSeries [] x = refl
evaluatePolynomialAsFinitePowerSeries
    (coefficient ∷ coefficients) x =
  cong (λ value → coefficient Add.+ x Mul.· value)
    (evaluatePolynomialAsFinitePowerSeries coefficients x)
  ∙ sym
      (polynomialCoefficientPartialSumStep
        coefficient coefficients x (length coefficients))


polynomialCoefficientSequence-zeroAfterLength :
  ∀ coefficients n →
  polynomialCoefficientSequence coefficients
    (length coefficients +ℕ n) ≡ zeroℝ
polynomialCoefficientSequence-zeroAfterLength [] n = refl
polynomialCoefficientSequence-zeroAfterLength
    (coefficient ∷ coefficients) n =
  polynomialCoefficientSequence-zeroAfterLength coefficients n


polynomialPowerSeriesTerm-zeroAfterLength :
  ∀ coefficients x n →
  powerSeriesTerms
    (polynomialCoefficientSequence coefficients) x
    (n +ℕ length coefficients) ≡ zeroℝ
polynomialPowerSeriesTerm-zeroAfterLength coefficients x n =
  cong
    (Mul._· x ^ⁿ (n +ℕ length coefficients))
    (subst
      (λ index →
        polynomialCoefficientSequence coefficients index ≡ zeroℝ)
      (Nat.+-comm (length coefficients) n)
      (polynomialCoefficientSequence-zeroAfterLength coefficients n))
  ∙ mul-zero-left (x ^ⁿ (n +ℕ length coefficients))


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
    (Add._+
      powerSeriesTerms
        (polynomialCoefficientSequence coefficients) x
        (n +ℕ length coefficients))
    (polynomialPowerSeriesPartialSumStable coefficients x n)
  ∙ cong
      (partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence coefficients) x)
        (length coefficients) Add.+_)
      (polynomialPowerSeriesTerm-zeroAfterLength coefficients x n)
  ∙ add-zero-right
      (partialSum
        (powerSeriesTerms
          (polynomialCoefficientSequence coefficients) x)
        (length coefficients))


polynomialPowerSeriesPartialSumStableAbove :
  ∀ coefficients x n →
  length coefficients ℕ.≤ n →
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
    (polynomialPowerSeriesPartialSumStable coefficients x count)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms (polynomialCoefficientSequence coefficients) x


-- Finite support gives an explicit stable partial sum.  Its convergence is
-- nevertheless stated through the ordinary radiuswise limit interface.

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
    ∣ length coefficients , (λ n length≤n →
      sym (polynomialPowerSeriesPartialSumStableAbove
        coefficients x n length≤n)) ∣₁
    (constantIsLimitSequence stable-sum)
  where
  terms : RealSequence
  terms =
    powerSeriesTerms (polynomialCoefficientSequence coefficients) x

  stable-sum : Real.ℝ
  stable-sum = partialSum terms (length coefficients)


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
    powerSeriesTerms (polynomialCoefficientSequence coefficients) x
