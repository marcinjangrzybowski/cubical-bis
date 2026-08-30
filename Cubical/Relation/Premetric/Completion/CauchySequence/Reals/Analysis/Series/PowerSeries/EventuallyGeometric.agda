module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.EventuallyGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Polynomial


EventuallyScaledGeometricCoefficientsFrom :
  ℕ → Real.ℝ → Real.ℝ → RealSequence → Type
EventuallyScaledGeometricCoefficientsFrom
  start coefficient ratio coefficients =
    dropSeries start coefficients ≡
      scaledGeometricTerms coefficient ratio


private
  rearrangeFourFactors : ∀ (a b c d : Real.ℝ) →
    (a Mul.· b) Mul.· (c Mul.· d)
      ≡
    (a Mul.· c) Mul.· (b Mul.· d)
  rearrangeFourFactors a b c d =
      sym (mul-assoc a b (c Mul.· d))
    ∙ cong (a Mul.·_) (mul-assoc b c d)
    ∙ cong (λ value → a Mul.· (value Mul.· d))
        (mul-comm b c)
    ∙ cong (a Mul.·_) (sym (mul-assoc c b d))
    ∙ mul-assoc a c (b Mul.· d)

  contractionPowersTendToZero : ∀ value →
    RationalContractionBound value →
    GeometricPowersTendToZero value
  contractionPowersTendToZero value contraction =
    summableTermsTendToZero
      (geometricTerms value)
      (geometricSeriesIsSummableByRationalContraction
        value contraction)

  absContraction→value<1 : ∀ value →
    Abs.absℝ value <ℝ Real.ιℚ 1 →
    value <ℝ Real.ιℚ 1
  absContraction→value<1 value abs-value<1 =
    ≤<ℝ-trans value (Abs.absℝ value) (Real.ιℚ 1)
      (x≤abs value) abs-value<1

  absContractionPowersTendToZero : ∀ value →
    Abs.absℝ value <ℝ Real.ιℚ 1 →
    GeometricPowersTendToZero value
  absContractionPowersTendToZero value abs-value<1 =
    summableTermsTendToZero
      (geometricTerms value)
      (geometricSeriesIsSummableOfAbs<1 value abs-value<1)


eventuallyGeometricPowerSeriesTail :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  dropSeries start (powerSeriesTerms coefficients x)
    ≡
  scaledGeometricTerms
    (coefficient Mul.· x ^ⁿ start)
    (ratio Mul.· x)
eventuallyGeometricPowerSeriesTail
  start coefficient ratio coefficients x coefficient-tail =
    funExt pointwise
  where
  pointwise : ∀ n →
    dropSeries start (powerSeriesTerms coefficients x) n
      ≡
    scaledGeometricTerms
      (coefficient Mul.· x ^ⁿ start)
      (ratio Mul.· x) n
  pointwise n =
      cong
        (Mul._· x ^ⁿ (n ℕ.+ start))
        (funExt⁻ coefficient-tail n)
    ∙ cong
        ((coefficient Mul.· ratio ^ⁿ n) Mul.·_)
        ( cong (x ^ⁿ_) (ℕ.+-comm n start)
        ∙ sym
            (ℝExponentiation.·-of-^-is-^-of-+
              x start n)
        )
    ∙ rearrangeFourFactors
        coefficient (ratio ^ⁿ n)
        (x ^ⁿ start) (x ^ⁿ n)
    ∙ cong
        ((coefficient Mul.· x ^ⁿ start) Mul.·_)
        (sym
          (ℝExponentiation.^-ldist-·
            ratio x n))


eventuallyGeometricPowerSeriesHasSum :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  HasSum
    (powerSeriesTerms coefficients x)
    ( partialSum (powerSeriesTerms coefficients x) start
      Add.+
      (coefficient Mul.· x ^ⁿ start) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (rationalContractionBound→x<1
            (ratio Mul.· x) contraction)
    )
eventuallyGeometricPowerSeriesHasSum
  start coefficient ratio coefficients x
  coefficient-tail contraction =
    eventuallyScaledGeometricFromHasSum
      start
      (coefficient Mul.· x ^ⁿ start)
      (ratio Mul.· x)
      (powerSeriesTerms coefficients x)
      (eventuallyGeometricPowerSeriesTail
        start coefficient ratio coefficients x coefficient-tail)
      (rationalContractionBound→x<1
        (ratio Mul.· x) contraction)
      (contractionPowersTendToZero
        (ratio Mul.· x) contraction)


-- The sharp open condition is sufficient without exposing a chosen
-- rational majorant.  Unlike the existential summability proof obtained by
-- truncation elimination, the displayed sum is available directly: its
-- reciprocal only needs the proof-irrelevant inequality ratio · x < 1.

eventuallyGeometricPowerSeriesHasSumOfAbs<1 :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  (abs-ratio-x<1 :
    Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1) →
  HasSum
    (powerSeriesTerms coefficients x)
    ( partialSum (powerSeriesTerms coefficients x) start
      Add.+
      (coefficient Mul.· x ^ⁿ start) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (absContraction→value<1
            (ratio Mul.· x) abs-ratio-x<1)
    )
eventuallyGeometricPowerSeriesHasSumOfAbs<1
  start coefficient ratio coefficients x
  coefficient-tail abs-ratio-x<1 =
    eventuallyScaledGeometricFromHasSum
      start
      (coefficient Mul.· x ^ⁿ start)
      (ratio Mul.· x)
      (powerSeriesTerms coefficients x)
      (eventuallyGeometricPowerSeriesTail
        start coefficient ratio coefficients x coefficient-tail)
      (absContraction→value<1
        (ratio Mul.· x) abs-ratio-x<1)
      (absContractionPowersTendToZero
        (ratio Mul.· x) abs-ratio-x<1)


eventuallyGeometricPowerSeriesSummableOfAbs<1 :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1 →
  PowerSeriesSummableAt coefficients x
eventuallyGeometricPowerSeriesSummableOfAbs<1
  start coefficient ratio coefficients x
  coefficient-tail abs-ratio-x<1 =
    _ , eventuallyGeometricPowerSeriesHasSumOfAbs<1
          start coefficient ratio coefficients x
          coefficient-tail abs-ratio-x<1


eventuallyGeometricPowerSeriesSummable :
  ∀ start coefficient ratio coefficients x →
  EventuallyScaledGeometricCoefficientsFrom
    start coefficient ratio coefficients →
  RationalContractionBound (ratio Mul.· x) →
  PowerSeriesSummableAt coefficients x
eventuallyGeometricPowerSeriesSummable
  start coefficient ratio coefficients x
  coefficient-tail contraction =
    partialSum (powerSeriesTerms coefficients x) start
      Add.+
      (coefficient Mul.· x ^ⁿ start) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (rationalContractionBound→x<1
            (ratio Mul.· x) contraction)
    , eventuallyGeometricPowerSeriesHasSum
        start coefficient ratio coefficients x
        coefficient-tail contraction


powerSeriesValue-eventuallyGeometric :
  ∀ start coefficient ratio coefficients x →
  (coefficient-tail :
    EventuallyScaledGeometricCoefficientsFrom
      start coefficient ratio coefficients) →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  (summable : PowerSeriesSummableAt coefficients x) →
  powerSeriesValue coefficients x summable
    ≡
  partialSum (powerSeriesTerms coefficients x) start
    Add.+
    (coefficient Mul.· x ^ⁿ start) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (rationalContractionBound→x<1
          (ratio Mul.· x) contraction)
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
  List Real.ℝ → Real.ℝ → Real.ℝ → RealSequence
polynomialGeometricCoefficients [] coefficient ratio n =
  coefficient Mul.· ratio ^ⁿ n
polynomialGeometricCoefficients
  (head ∷ prefix) coefficient ratio ℕ.zero =
    head
polynomialGeometricCoefficients
  (head ∷ prefix) coefficient ratio (ℕ.suc n) =
    polynomialGeometricCoefficients prefix coefficient ratio n


polynomialGeometricCoefficients-afterLength :
  ∀ prefix coefficient ratio n →
  polynomialGeometricCoefficients
      prefix coefficient ratio (length prefix ℕ.+ n)
    ≡
  coefficient Mul.· ratio ^ⁿ n
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
    (polynomialGeometricCoefficients prefix coefficient ratio)
polynomialGeometricCoefficients-tail prefix coefficient ratio =
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
  polynomialGeometricCoefficients prefix coefficient ratio n
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
          prefix coefficient ratio) x)
      (length prefix)
    ≡
  evaluatePolynomial prefix x
polynomialGeometricPrefixValue prefix coefficient ratio x =
    partialSum-pointwiseBefore
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio) x)
      (powerSeriesTerms
        (polynomialCoefficientSequence prefix) x)
      (length prefix)
      (λ n n<length →
        cong
          (Mul._· x ^ⁿ n)
          (polynomialGeometricCoefficients-beforeLength
            prefix coefficient ratio n n<length))
  ∙ sym (evaluatePolynomialAsFinitePowerSeries prefix x)


polynomialGeometricPowerSeriesHasSum :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  HasSum
    (powerSeriesTerms
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x)
    ( evaluatePolynomial prefix x Add.+
      (coefficient Mul.· x ^ⁿ length prefix) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (rationalContractionBound→x<1
            (ratio Mul.· x) contraction)
    )
polynomialGeometricPowerSeriesHasSum
  prefix coefficient ratio x contraction =
    subst
      (HasSum terms)
      (cong (Add._+ tail-value)
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
    polynomialGeometricCoefficients prefix coefficient ratio

  terms : RealSequence
  terms = powerSeriesTerms coefficients x

  tail-value : Real.ℝ
  tail-value =
    (coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (rationalContractionBound→x<1
          (ratio Mul.· x) contraction)


polynomialGeometricPowerSeriesSummable :
  ∀ prefix coefficient ratio x →
  RationalContractionBound (ratio Mul.· x) →
  PowerSeriesSummableAt
    (polynomialGeometricCoefficients
      prefix coefficient ratio) x
polynomialGeometricPowerSeriesSummable
  prefix coefficient ratio x contraction =
    evaluatePolynomial prefix x Add.+
      (coefficient Mul.· x ^ⁿ length prefix) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (rationalContractionBound→x<1
            (ratio Mul.· x) contraction)
    , polynomialGeometricPowerSeriesHasSum
        prefix coefficient ratio x contraction


powerSeriesValue-polynomialGeometric :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x summable
    ≡
  evaluatePolynomial prefix x Add.+
    (coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (rationalContractionBound→x<1
          (ratio Mul.· x) contraction)
powerSeriesValue-polynomialGeometric
  prefix coefficient ratio x contraction summable =
    seriesSumIndependent
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio) x)
      summable
      (polynomialGeometricPowerSeriesSummable
        prefix coefficient ratio x contraction)


-- Sharp, witness-free variants.  These retain the exact rational expression
-- while replacing the displayed rational contraction bound by |ratio·x| < 1.

polynomialGeometricPowerSeriesHasSumOfAbs<1 :
  ∀ prefix coefficient ratio x →
  (abs-ratio-x<1 :
    Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1) →
  HasSum
    (powerSeriesTerms
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x)
    ( evaluatePolynomial prefix x Add.+
      (coefficient Mul.· x ^ⁿ length prefix) Mul.·
        geometricReciprocal
          (ratio Mul.· x)
          (absContraction→value<1
            (ratio Mul.· x) abs-ratio-x<1)
    )
polynomialGeometricPowerSeriesHasSumOfAbs<1
  prefix coefficient ratio x abs-ratio-x<1 =
    subst
      (HasSum terms)
      (cong (Add._+ tail-value)
        (polynomialGeometricPrefixValue
          prefix coefficient ratio x))
      (eventuallyGeometricPowerSeriesHasSumOfAbs<1
        (length prefix)
        coefficient ratio coefficients x
        (polynomialGeometricCoefficients-tail
          prefix coefficient ratio)
        abs-ratio-x<1)
  where
  coefficients : RealSequence
  coefficients =
    polynomialGeometricCoefficients prefix coefficient ratio

  terms : RealSequence
  terms = powerSeriesTerms coefficients x

  tail-value : Real.ℝ
  tail-value =
    (coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (absContraction→value<1
          (ratio Mul.· x) abs-ratio-x<1)


polynomialGeometricPowerSeriesSummableOfAbs<1 :
  ∀ prefix coefficient ratio x →
  Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1 →
  PowerSeriesSummableAt
    (polynomialGeometricCoefficients
      prefix coefficient ratio) x
polynomialGeometricPowerSeriesSummableOfAbs<1
  prefix coefficient ratio x abs-ratio-x<1 =
    _ , polynomialGeometricPowerSeriesHasSumOfAbs<1
          prefix coefficient ratio x abs-ratio-x<1


powerSeriesValue-polynomialGeometricOfAbs<1 :
  ∀ prefix coefficient ratio x →
  (abs-ratio-x<1 :
    Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x summable
    ≡
  evaluatePolynomial prefix x Add.+
    (coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (absContraction→value<1
          (ratio Mul.· x) abs-ratio-x<1)
powerSeriesValue-polynomialGeometricOfAbs<1
  prefix coefficient ratio x abs-ratio-x<1 summable =
    seriesSumIndependent
      (powerSeriesTerms
        (polynomialGeometricCoefficients
          prefix coefficient ratio) x)
      summable
      (polynomialGeometricPowerSeriesSummableOfAbs<1
        prefix coefficient ratio x abs-ratio-x<1)
