module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


geometricReciprocal : ∀ ratio →
  ratio <ℝ oneℝ → Real.ℝ
geometricReciprocal ratio ratio<one =
  positiveReciprocal
    (oneℝ Group.- ratio)
    (strictlyPositiveDifference≪ ratio oneℝ ratio<one)


scaledGeometricTerms : Real.ℝ → Real.ℝ → RealSequence
scaledGeometricTerms coefficient ratio =
  scaleSeries coefficient (geometricTerms ratio)


scaledGeometricSeriesHasSum : ∀ coefficient ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  HasSum
    (scaledGeometricTerms coefficient ratio)
    (coefficient Mul.· geometricReciprocal ratio ratio<one)
scaledGeometricSeriesHasSum
    coefficient ratio ratio<one powers-limit =
  scaleHasSum
    coefficient
    (geometricTerms ratio)
    (geometricReciprocal ratio ratio<one)
    (geometricSeriesHasSum ratio ratio<one powers-limit)


scaledGeometricSeriesSummable : ∀ coefficient ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  Summable (scaledGeometricTerms coefficient ratio)
scaledGeometricSeriesSummable
    coefficient ratio ratio<one powers-limit =
  coefficient Mul.· geometricReciprocal ratio ratio<one
  , scaledGeometricSeriesHasSum
      coefficient ratio ratio<one powers-limit


seriesSum-scaledGeometric : ∀ coefficient ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero ratio) →
  (summable : Summable
    (scaledGeometricTerms coefficient ratio)) →
  seriesSum
      (scaledGeometricTerms coefficient ratio) summable
    ≡
  coefficient Mul.· geometricReciprocal ratio ratio<one
seriesSum-scaledGeometric
    coefficient ratio ratio<one powers-limit summable =
  seriesSumIndependent
    (scaledGeometricTerms coefficient ratio)
    summable
    (scaledGeometricSeriesSummable
      coefficient ratio ratio<one powers-limit)


shiftedGeometricTerms : ℕ → Real.ℝ → RealSequence
shiftedGeometricTerms start ratio =
  dropSeries start (geometricTerms ratio)


shiftedGeometricTerms-scale : ∀ start ratio →
  shiftedGeometricTerms start ratio ≡
  scaledGeometricTerms (ratio ^ⁿ start) ratio
shiftedGeometricTerms-scale start ratio =
  funExt λ n →
    cong (ratio ^ⁿ_) (ℕ.+-comm n start)
    ∙ sym
        (ℝExponentiation.·-of-^-is-^-of-+
          ratio start n)


shiftedGeometricSeriesHasSum : ∀ start ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  HasSum
    (shiftedGeometricTerms start ratio)
    (ratio ^ⁿ start Mul.·
      geometricReciprocal ratio ratio<one)
shiftedGeometricSeriesHasSum
    start ratio ratio<one powers-limit =
  subst
    (λ terms →
      HasSum terms
        (ratio ^ⁿ start Mul.·
          geometricReciprocal ratio ratio<one))
    (sym (shiftedGeometricTerms-scale start ratio))
    (scaledGeometricSeriesHasSum
      (ratio ^ⁿ start) ratio ratio<one powers-limit)


shiftedGeometricSeriesSummable : ∀ start ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  Summable (shiftedGeometricTerms start ratio)
shiftedGeometricSeriesSummable
    start ratio ratio<one powers-limit =
  ratio ^ⁿ start Mul.·
    geometricReciprocal ratio ratio<one
  , shiftedGeometricSeriesHasSum
      start ratio ratio<one powers-limit


seriesSum-shiftedGeometric : ∀ start ratio →
  (ratio<one : ratio <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero ratio) →
  (summable : Summable (shiftedGeometricTerms start ratio)) →
  seriesSum (shiftedGeometricTerms start ratio) summable ≡
  ratio ^ⁿ start Mul.·
    geometricReciprocal ratio ratio<one
seriesSum-shiftedGeometric
    start ratio ratio<one powers-limit summable =
  seriesSumIndependent
    (shiftedGeometricTerms start ratio)
    summable
    (shiftedGeometricSeriesSummable
      start ratio ratio<one powers-limit)


EventuallyScaledGeometricFrom :
  ℕ → Real.ℝ → Real.ℝ → RealSequence → Type₀
EventuallyScaledGeometricFrom start coefficient ratio terms =
  dropSeries start terms ≡
  scaledGeometricTerms coefficient ratio


-- The unindexed notion truncates the cutoff.  This is enough for existence
-- of a sum, but not for projecting a particular cutoff-dependent formula.

EventuallyScaledGeometric :
  Real.ℝ → Real.ℝ → RealSequence → Type₀
EventuallyScaledGeometric coefficient ratio terms =
  ∥ Σ[ start ∈ ℕ ]
      EventuallyScaledGeometricFrom
        start coefficient ratio terms ∥₁


isPropEventuallyScaledGeometric : ∀ coefficient ratio terms →
  isProp (EventuallyScaledGeometric coefficient ratio terms)
isPropEventuallyScaledGeometric coefficient ratio terms = squash₁


eventuallyScaledGeometricFromHasSum :
  ∀ start coefficient ratio terms →
  EventuallyScaledGeometricFrom start coefficient ratio terms →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  HasSum terms
    (partialSum terms start Add.+
      coefficient Mul.· geometricReciprocal ratio ratio<one)
eventuallyScaledGeometricFromHasSum
    start coefficient ratio terms tail-path
    ratio<one powers-limit =
  dropSeriesReflectsHasSum
    start terms
    (coefficient Mul.· geometricReciprocal ratio ratio<one)
    tail-has-sum
  where
  tail-has-sum :
    HasSum
      (dropSeries start terms)
      (coefficient Mul.· geometricReciprocal ratio ratio<one)
  tail-has-sum =
    subst
      (λ sequence →
        HasSum sequence
          (coefficient Mul.·
            geometricReciprocal ratio ratio<one))
      (sym tail-path)
      (scaledGeometricSeriesHasSum
        coefficient ratio ratio<one powers-limit)


eventuallyScaledGeometricFromSummable :
  ∀ start coefficient ratio terms →
  EventuallyScaledGeometricFrom start coefficient ratio terms →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  Summable terms
eventuallyScaledGeometricFromSummable
    start coefficient ratio terms tail-path
    ratio<one powers-limit =
  partialSum terms start Add.+
    coefficient Mul.· geometricReciprocal ratio ratio<one
  , eventuallyScaledGeometricFromHasSum
      start coefficient ratio terms tail-path
      ratio<one powers-limit


eventuallyScaledGeometricSummable : ∀ coefficient ratio terms →
  EventuallyScaledGeometric coefficient ratio terms →
  (ratio<one : ratio <ℝ oneℝ) →
  GeometricPowersTendToZero ratio →
  Summable terms
eventuallyScaledGeometricSummable
    coefficient ratio terms merely-tail ratio<one powers-limit =
  PT.rec
    (isPropSummable terms)
    (λ where
      (start , tail-path) →
        eventuallyScaledGeometricFromSummable
          start coefficient ratio terms tail-path
          ratio<one powers-limit)
    merely-tail


-- If the cutoff is only known merely, the exact formula must retain that
-- truncation.  Returning an untruncated numerical formula here would amount
-- to selecting a cutoff from a propositionally truncated witness.

eventuallyScaledGeometricHasSumWitness :
  ∀ coefficient ratio terms →
  EventuallyScaledGeometric coefficient ratio terms →
  (ratio<one : ratio <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero ratio) →
  ∥ Σ[ start ∈ ℕ ]
      HasSum terms
        (partialSum terms start Add.+
          coefficient Mul.·
            geometricReciprocal ratio ratio<one) ∥₁
eventuallyScaledGeometricHasSumWitness
    coefficient ratio terms merely-tail ratio<one powers-limit =
  PT.map
    (λ where
      (start , tail-path) →
        start , eventuallyScaledGeometricFromHasSum
          start coefficient ratio terms tail-path
          ratio<one powers-limit)
    merely-tail


seriesSum-eventuallyScaledGeometricWitness :
  ∀ coefficient ratio terms →
  (summable : Summable terms) →
  EventuallyScaledGeometric coefficient ratio terms →
  (ratio<one : ratio <ℝ oneℝ) →
  (powers-limit : GeometricPowersTendToZero ratio) →
  ∥ Σ[ start ∈ ℕ ]
      seriesSum terms summable ≡
      partialSum terms start Add.+
        coefficient Mul.·
          geometricReciprocal ratio ratio<one ∥₁
seriesSum-eventuallyScaledGeometricWitness
    coefficient ratio terms summable merely-tail
    ratio<one powers-limit =
  PT.map
    (λ where
      (start , tail-path) →
        start , seriesSumIndependent
          terms summable
          (eventuallyScaledGeometricFromSummable
            start coefficient ratio terms tail-path
            ratio<one powers-limit))
    merely-tail
