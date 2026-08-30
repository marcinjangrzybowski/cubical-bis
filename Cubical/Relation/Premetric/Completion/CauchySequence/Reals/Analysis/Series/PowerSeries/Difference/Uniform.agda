module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform


ClosedAbsRadiusPair : Real.ℝ → Type
ClosedAbsRadiusPair radius =
  ClosedAbsRadius radius × ClosedAbsRadius radius


ClosedAbsRadiusPairPremetricSpace :
  Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPairPremetricSpace radius =
  PremetricProduct
    (ClosedAbsRadiusPremetricSpace radius)
    (ClosedAbsRadiusPremetricSpace radius)


closedAbsRadiusPairLeft :
  ∀ radius → ClosedAbsRadiusPair radius → Real.ℝ
closedAbsRadiusPairLeft radius point = fst (fst point)


closedAbsRadiusPairRight :
  ∀ radius → ClosedAbsRadiusPair radius → Real.ℝ
closedAbsRadiusPairRight radius point = fst (snd point)


closedAbsRadiusPairLeftIsContinuous :
  ∀ radius →
  isContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    (closedAbsRadiusPairLeft radius)
    (snd Real.ℝPremetricSpace)
closedAbsRadiusPairLeftIsContinuous radius point
  .IsContinuousAt.pres≈ ε =
  return
    ( ε
    , λ _ point≈other → fst point≈other
    )


closedAbsRadiusPairRightIsContinuous :
  ∀ radius →
  isContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    (closedAbsRadiusPairRight radius)
    (snd Real.ℝPremetricSpace)
closedAbsRadiusPairRightIsContinuous radius point
  .IsContinuousAt.pres≈ ε =
  return
    ( ε
    , λ _ point≈other → snd point≈other
    )


powerSeriesDifferenceFactorOnClosedRadius :
  RealSequence → ∀ radius →
  ClosedAbsRadiusPair radius → RealSequence
powerSeriesDifferenceFactorOnClosedRadius coefficients radius point =
  powerSeriesDifferenceFactor coefficients
    (closedAbsRadiusPairLeft radius point)
    (closedAbsRadiusPairRight radius point)


PowerSeriesDifferenceFactorUniformlyCauchyOnRadius :
  RealSequence → Real.ℝ → Type
PowerSeriesDifferenceFactorUniformlyCauchyOnRadius coefficients radius =
  UniformlyCauchySeries
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)


PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius :
  RealSequence → Real.ℝ → Type
PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
  coefficients radius =
  UniformlyAbsolutelyCauchySeries
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)


-- The coefficient-majorant premise already proves nonnegativity of the
-- majorant.  This is the first point where the native API is strictly less
-- redundant than the older CauchyRealsP statement.

powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms (formalDerivativeMajorant majorant) radius) →
  PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
    coefficients radius
powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
  coefficients majorant radius majorized derivative-majorant-cauchy =
  familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
    (powerSeriesTerms (formalDerivativeMajorant majorant) radius)
    dominates derivative-majorant-cauchy
  where
  dominates : ∀ point n →
    Abs.absℝ
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
      ≤ℝ
    powerSeriesTerms (formalDerivativeMajorant majorant) radius n
  dominates point n =
    powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
      coefficients majorant
      (closedAbsRadiusPairLeft radius point)
      (closedAbsRadiusPairRight radius point)
      radius majorized radius-nonnegative
      (snd (fst point)) (snd (snd point)) n
    where
    radius-nonnegative : Real.ιℚ 0 ≤ℝ radius
    radius-nonnegative =
      ≤ℝ-trans
        (Real.ιℚ 0)
        (Abs.absℝ (closedAbsRadiusPairLeft radius point))
        radius
        (zero≤abs (closedAbsRadiusPairLeft radius point))
        (snd (fst point))


powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin :
  ∀ coefficients majorant inner-radius outer-radius →
  CoefficientMajorizedBy coefficients majorant →
  Real.ιℚ 0 ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) outer-radius) →
  PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer outer-cauchy =
  powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
    coefficients majorant inner-radius majorized
    (nonnegativePowerSeriesIsCauchyWithinRadius
      (formalDerivativeMajorant majorant)
      inner-radius outer-radius
      (formalDerivativeMajorant-nonnegative majorant
        (coefficientMajorantIsNonnegative
          coefficients majorant majorized))
      inner-nonnegative inner≤outer outer-cauchy)


powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms (formalDerivativeMajorant majorant) radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius coefficients radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
  coefficients majorant radius majorized derivative-majorant-cauchy =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
    (powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
      coefficients majorant radius majorized derivative-majorant-cauchy)


powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin :
  ∀ coefficients majorant inner-radius outer-radius →
  CoefficientMajorizedBy coefficients majorant →
  Real.ιℚ 0 ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) outer-radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer outer-cauchy =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadiusPair inner-radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients inner-radius)
    (powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer outer-cauchy)


powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous :
  ∀ coefficients radius n →
  isContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    (λ point →
      powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
    (snd Real.ℝPremetricSpace)
powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
  coefficients radius n =
  powerSeriesDifferenceFactorOfContinuousIsContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    coefficients
    (closedAbsRadiusPairLeft radius)
    (closedAbsRadiusPairRight radius)
    (closedAbsRadiusPairLeftIsContinuous radius)
    (closedAbsRadiusPairRightIsContinuous radius)
    n


powerSeriesDifferenceFactorValueOnClosedRadius :
  ∀ coefficients radius →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius →
  ClosedAbsRadiusPair radius → Real.ℝ
powerSeriesDifferenceFactorValueOnClosedRadius
  coefficients radius uniform =
  uniformSeriesValue
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
    uniform


powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous :
  ∀ coefficients radius
    (uniform :
      PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
        coefficients radius) →
  isContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    (powerSeriesDifferenceFactorValueOnClosedRadius
      coefficients radius uniform)
    (snd Real.ℝPremetricSpace)
powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
  coefficients radius uniform =
  uniformSeriesValueIsContinuous
    (snd (ClosedAbsRadiusPairPremetricSpace radius))
    (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
    uniform
    (powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
      coefficients radius)
