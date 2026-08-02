module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.EventuallyGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
  using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Affine
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial

EventuallyScaledGeometricCoefficientsFrom :
  ℕ → ℝ → ℝ → RealSequence → Type
EventuallyScaledGeometricCoefficientsFrom
  start coefficient ratio coefficients =
    dropSeries start coefficients
      ≡
    scaledGeometricTerms coefficient ratio

eventuallyGeometricPowerSeriesTail :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  dropSeries start
      (powerSeriesTerms coefficients x)
    ≡
  scaledGeometricTerms
    (coefficient · x ^ⁿ start)
    (ratio · x)
eventuallyGeometricPowerSeriesTail
  start coefficient ratio coefficients x
  coefficient-tail =
    funExt pointwise
  where
  rearrange : ∀ (p q r s : ℝ) →
    (p · q) · (r · s)
      ≡
    (p · r) · (q · s)
  rearrange p q r s =
    mulAssoc p q (r · s)
    ∙ cong (p ·_)
        (sym (mulAssoc q r s))
    ∙ cong (λ z → p · (z · s))
        (mulComm q r)
    ∙ cong (p ·_)
        (mulAssoc r q s)
    ∙ sym (mulAssoc p r (q · s))

  pointwise : ∀ n →
    dropSeries start
        (powerSeriesTerms coefficients x) n
      ≡
    scaledGeometricTerms
      (coefficient · x ^ⁿ start)
      (ratio · x) n
  pointwise n =
    cong
      (_· x ^ⁿ (n ℕ.+ start))
      (funExt⁻ coefficient-tail n)
    ∙ cong
        ((coefficient · ratio ^ⁿ n) ·_)
        ( cong (x ^ⁿ_)
            (ℕ.+-comm n start)
        ∙ sym
            (ℝExponentiation.·-of-^-is-^-of-+
              x start n)
        )
    ∙ rearrange
        coefficient (ratio ^ⁿ n)
        (x ^ⁿ start) (x ^ⁿ n)
    ∙ cong
        ((coefficient · x ^ⁿ start) ·_)
        (sym
          (ℝExponentiation.^-ldist-·
            ratio x n))

eventuallyGeometricPowerSeriesHasSum :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  (contraction :
    RationalContractionBound (ratio · x)) →
  HasSum
    (powerSeriesTerms coefficients x)
    ( partialSum
        (powerSeriesTerms coefficients x)
        start
    + (coefficient · x ^ⁿ start)
      · geometricReciprocal
          (ratio · x) contraction
    )
eventuallyGeometricPowerSeriesHasSum
  start coefficient ratio coefficients x
  coefficient-tail contraction =
    eventuallyScaledGeometricHasSum
      start
      (coefficient · x ^ⁿ start)
      (ratio · x)
      (powerSeriesTerms coefficients x)
      (eventuallyGeometricPowerSeriesTail
        start coefficient ratio coefficients x
        coefficient-tail)
      contraction

eventuallyGeometricPowerSeriesSummable :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  RationalContractionBound (ratio · x) →
  PowerSeriesSummableAt coefficients x
eventuallyGeometricPowerSeriesSummable
  start coefficient ratio coefficients x
  coefficient-tail contraction =
    partialSum
      (powerSeriesTerms coefficients x)
      start
      + (coefficient · x ^ⁿ start)
        · geometricReciprocal
            (ratio · x) contraction
    , eventuallyGeometricPowerSeriesHasSum
        start coefficient ratio coefficients x
        coefficient-tail contraction

powerSeriesValue-eventuallyGeometric :
  ∀ start coefficient ratio coefficients x →
  (coefficient-tail :
    EventuallyScaledGeometricCoefficientsFrom
      start coefficient ratio coefficients) →
  (contraction :
    RationalContractionBound (ratio · x)) →
  (summable : PowerSeriesSummableAt coefficients x) →
  powerSeriesValue coefficients x summable
    ≡
  partialSum
      (powerSeriesTerms coefficients x)
      start
    + (coefficient · x ^ⁿ start)
      · geometricReciprocal
          (ratio · x) contraction
powerSeriesValue-eventuallyGeometric
  start coefficient ratio coefficients x
  coefficient-tail contraction summable =
    seriesSumIndependent
      (powerSeriesTerms coefficients x)
      summable
      (eventuallyGeometricPowerSeriesSummable
        start coefficient ratio coefficients x
        coefficient-tail contraction)

polynomialGeometricCoefficients :
  List ℝ → ℝ → ℝ → RealSequence
polynomialGeometricCoefficients
  [] coefficient ratio n =
    coefficient · ratio ^ⁿ n
polynomialGeometricCoefficients
  (head ∷ prefix) coefficient ratio ℕ.zero =
    head
polynomialGeometricCoefficients
  (head ∷ prefix) coefficient ratio (ℕ.suc n) =
    polynomialGeometricCoefficients
      prefix coefficient ratio n

polynomialGeometricCoefficients-afterLength :
  ∀ prefix coefficient ratio n →
  polynomialGeometricCoefficients
      prefix coefficient ratio
      (length prefix ℕ.+ n)
    ≡
  coefficient · ratio ^ⁿ n
polynomialGeometricCoefficients-afterLength
  [] coefficient ratio n =
    refl
polynomialGeometricCoefficients-afterLength
  (head ∷ prefix) coefficient ratio n =
    polynomialGeometricCoefficients-afterLength
      prefix coefficient ratio n

polynomialGeometricCoefficients-tail :
  ∀ prefix coefficient ratio →
  EventuallyScaledGeometricCoefficientsFrom
    (length prefix) coefficient ratio
    (polynomialGeometricCoefficients
      prefix coefficient ratio)
polynomialGeometricCoefficients-tail
  prefix coefficient ratio =
    funExt λ n →
      cong
        (polynomialGeometricCoefficients
          prefix coefficient ratio)
        (ℕ.+-comm n (length prefix))
      ∙ polynomialGeometricCoefficients-afterLength
          prefix coefficient ratio n

polynomialGeometricCoefficients-beforeLength :
  ∀ prefix coefficient ratio n →
  n ℕ.< length prefix →
  polynomialGeometricCoefficients
      prefix coefficient ratio n
    ≡
  polynomialCoefficientSequence prefix n
polynomialGeometricCoefficients-beforeLength
  [] coefficient ratio n n<zero =
    ⊥.rec (ℕ.¬-<-zero n<zero)
polynomialGeometricCoefficients-beforeLength
  (head ∷ prefix) coefficient ratio ℕ.zero zero<length =
    refl
polynomialGeometricCoefficients-beforeLength
  (head ∷ prefix) coefficient ratio (ℕ.suc n) suc-n<length =
    polynomialGeometricCoefficients-beforeLength
      prefix coefficient ratio n
      (ℕ.pred-≤-pred suc-n<length)

polynomialGeometricPrefixValue :
  ∀ prefix coefficient ratio x →
  partialSum
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio)
        x)
      (length prefix)
    ≡
  evaluatePolynomial prefix x
polynomialGeometricPrefixValue
  prefix coefficient ratio x =
    partialSum-pointwiseBefore
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio)
        x)
      (powerSeriesTerms
        (polynomialCoefficientSequence prefix)
        x)
      (length prefix)
      (λ n n<length →
        cong
          (_· x ^ⁿ n)
          (polynomialGeometricCoefficients-beforeLength
            prefix coefficient ratio n n<length))
    ∙ sym
        (evaluatePolynomialAsFinitePowerSeries
          prefix x)

polynomialGeometricPowerSeriesHasSum :
  ∀ prefix coefficient ratio x →
  (contraction :
    RationalContractionBound (ratio · x)) →
  HasSum
    (powerSeriesTerms
      (polynomialGeometricCoefficients
        prefix coefficient ratio)
      x)
    ( evaluatePolynomial prefix x
    + (coefficient · x ^ⁿ length prefix)
      · geometricReciprocal
          (ratio · x) contraction
    )
polynomialGeometricPowerSeriesHasSum
  prefix coefficient ratio x contraction =
    subst
      (HasSum terms)
      (cong (_+ tail-value)
        (polynomialGeometricPrefixValue
          prefix coefficient ratio x))
      (eventuallyGeometricPowerSeriesHasSum
        (length prefix)
        coefficient ratio coefficients x
        (polynomialGeometricCoefficients-tail
          prefix coefficient ratio)
        contraction)
  where
  coefficients : RealSequence
  coefficients =
    polynomialGeometricCoefficients
      prefix coefficient ratio

  terms : RealSequence
  terms =
    powerSeriesTerms coefficients x

  tail-value : ℝ
  tail-value =
    (coefficient · x ^ⁿ length prefix)
      · geometricReciprocal
          (ratio · x) contraction

polynomialGeometricPowerSeriesSummable :
  ∀ prefix coefficient ratio x →
  RationalContractionBound (ratio · x) →
  PowerSeriesSummableAt
    (polynomialGeometricCoefficients
      prefix coefficient ratio)
    x
polynomialGeometricPowerSeriesSummable
  prefix coefficient ratio x contraction =
    evaluatePolynomial prefix x
      + (coefficient · x ^ⁿ length prefix)
        · geometricReciprocal
            (ratio · x) contraction
    , polynomialGeometricPowerSeriesHasSum
        prefix coefficient ratio x contraction

powerSeriesValue-polynomialGeometric :
  ∀ prefix coefficient ratio x →
  (contraction :
    RationalContractionBound (ratio · x)) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio)
      x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio)
      x summable
    ≡
  evaluatePolynomial prefix x
    + (coefficient · x ^ⁿ length prefix)
      · geometricReciprocal
          (ratio · x) contraction
powerSeriesValue-polynomialGeometric
  prefix coefficient ratio x
  contraction summable =
    seriesSumIndependent
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio)
        x)
      summable
      (polynomialGeometricPowerSeriesSummable
        prefix coefficient ratio x contraction)
