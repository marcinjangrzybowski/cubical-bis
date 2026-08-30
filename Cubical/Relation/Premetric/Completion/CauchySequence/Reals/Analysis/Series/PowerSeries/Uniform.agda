module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Base using (fromNatℚ)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth


powerSeriesTermsOnClosedRadius :
  RealSequence → ∀ radius →
  ClosedAbsRadius radius → RealSequence
powerSeriesTermsOnClosedRadius coefficients radius point =
  powerSeriesTerms coefficients (fst point)


PowerSeriesUniformlyCauchyOnRadius :
  RealSequence → Real.ℝ → Type₀
PowerSeriesUniformlyCauchyOnRadius coefficients radius =
  UniformlyCauchySeries (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)


PowerSeriesUniformlyAbsolutelyCauchyOnRadius :
  RealSequence → Real.ℝ → Type₀
PowerSeriesUniformlyAbsolutelyCauchyOnRadius coefficients radius =
  UniformlyAbsolutelyCauchySeries (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)


-- The coefficient-majorant relation itself already implies that the
-- majorant coefficients are nonnegative.  Consequently the native theorem
-- does not retain the redundant nonnegativity argument from the older API.

powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries (powerSeriesTerms majorant radius) →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius coefficients radius
powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant radius coefficients-majorized majorant-cauchy =
  familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)
    (powerSeriesTerms majorant radius)
    dominates majorant-cauchy
  where
  dominates : ∀ point n →
    Abs.absℝ
      (powerSeriesTermsOnClosedRadius coefficients radius point n) ≤ℝ
    powerSeriesTerms majorant radius n
  dominates point n =
    powerSeriesTermAbsBoundByCoefficientMajorant
      coefficients majorant (fst point) radius
      coefficients-majorized (snd point) n


powerSeriesUniformlyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries (powerSeriesTerms majorant radius) →
  PowerSeriesUniformlyCauchyOnRadius coefficients radius
powerSeriesUniformlyCauchyByCoefficientMajorant
  coefficients majorant radius coefficients-majorized majorant-cauchy =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)
    (powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients majorant radius coefficients-majorized majorant-cauchy)


formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms (formalDerivativeMajorant majorant) radius) →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (formalDerivative coefficients) radius
formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant radius coefficients-majorized derivative-cauchy =
  powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    (formalDerivative coefficients)
    (formalDerivativeMajorant majorant) radius
    (formalDerivativePresCoefficientMajorant
      coefficients majorant coefficients-majorized)
    derivative-cauchy


formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms (formalDerivativeMajorant majorant) radius) →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative coefficients) radius
formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
  coefficients majorant radius coefficients-majorized derivative-cauchy =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius (formalDerivative coefficients) radius)
    (formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients majorant radius coefficients-majorized derivative-cauchy)


-- On a smaller nonnegative radius it suffices that the derivative majorant
-- series is Cauchy at an outer radius.  Majorant nonnegativity is derived
-- from the coefficient-majorant relation rather than requested separately.

opaque
  formalDerivativePowerSeriesUniformlyAbsolutelyCauchyWithin :
    ∀ coefficients majorant inner-radius outer-radius →
    CoefficientMajorizedBy coefficients majorant →
    zeroℝ ≤ℝ inner-radius →
    inner-radius ≤ℝ outer-radius →
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius) →
    PowerSeriesUniformlyAbsolutelyCauchyOnRadius
      (formalDerivative coefficients) inner-radius
  formalDerivativePowerSeriesUniformlyAbsolutelyCauchyWithin
    coefficients majorant inner-radius outer-radius
    coefficients-majorized inner-nonnegative inner≤outer outer-cauchy =
    formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients majorant inner-radius coefficients-majorized
      (nonnegativePowerSeriesIsCauchyWithinRadius
        (formalDerivativeMajorant majorant)
        inner-radius outer-radius
        (formalDerivativeMajorant-nonnegative majorant
          (coefficientMajorantIsNonnegative
            coefficients majorant coefficients-majorized))
        inner-nonnegative inner≤outer outer-cauchy)


  formalDerivativePowerSeriesUniformlyCauchyWithin :
    ∀ coefficients majorant inner-radius outer-radius →
    CoefficientMajorizedBy coefficients majorant →
    zeroℝ ≤ℝ inner-radius →
    inner-radius ≤ℝ outer-radius →
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius) →
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients) inner-radius
  formalDerivativePowerSeriesUniformlyCauchyWithin
    coefficients majorant inner-radius outer-radius
    coefficients-majorized inner-nonnegative inner≤outer outer-cauchy =
    uniformAbsoluteCauchySeriesIsUniformCauchy
      (ClosedAbsRadius inner-radius)
      (powerSeriesTermsOnClosedRadius
        (formalDerivative coefficients) inner-radius)
      (formalDerivativePowerSeriesUniformlyAbsolutelyCauchyWithin
        coefficients majorant inner-radius outer-radius
        coefficients-majorized inner-nonnegative inner≤outer outer-cauchy)


boundedPowerSeriesUniformlyAbsolutelyCauchy : ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients (Real.ιℚ (fst q))
boundedPowerSeriesUniformlyAbsolutelyCauchy
  C q coefficients coefficients-bounded q<1 =
  familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
    (ClosedAbsRadius (Real.ιℚ (fst q)))
    (powerSeriesTermsOnClosedRadius coefficients (Real.ιℚ (fst q)))
    (coefficientGeometricMajorant C q)
    (λ point n →
      powerSeriesTermAbsBound C q coefficients (fst point)
        coefficients-bounded (snd point) n)
    (coefficientGeometricMajorantIsCauchy C q q<1)


boundedPowerSeriesUniformlyCauchy : ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyCauchyOnRadius
    coefficients (Real.ιℚ (fst q))
boundedPowerSeriesUniformlyCauchy
  C q coefficients coefficients-bounded q<1 =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadius (Real.ιℚ (fst q)))
    (powerSeriesTermsOnClosedRadius coefficients (Real.ιℚ (fst q)))
    (boundedPowerSeriesUniformlyAbsolutelyCauchy
      C q coefficients coefficients-bounded q<1)


-- Mertens turns the square of the geometric series into the linear-growth
-- majorant (n + 1)qⁿ.  This discharges the derivative-majorant premise for
-- every bounded coefficient sequence on a positive rational radius q < 1.

boundedPowerSeriesFormalDerivativeUniformlyAbsolutelyCauchy :
  ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (formalDerivative coefficients) (Real.ιℚ (fst q))
boundedPowerSeriesFormalDerivativeUniformlyAbsolutelyCauchy
  C q coefficients coefficients-bounded q<1 =
  formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    coefficients (constantCoefficientMajorant C) (Real.ιℚ (fst q))
    (coefficientAbsBoundIsMajorized C coefficients coefficients-bounded)
    (formalDerivativeConstantMajorantIsCauchyAtPositiveRational C q q<1)


boundedPowerSeriesFormalDerivativeUniformlyCauchy :
  ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative coefficients) (Real.ιℚ (fst q))
boundedPowerSeriesFormalDerivativeUniformlyCauchy
  C q coefficients coefficients-bounded q<1 =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    (ClosedAbsRadius (Real.ιℚ (fst q)))
    (powerSeriesTermsOnClosedRadius
      (formalDerivative coefficients) (Real.ιℚ (fst q)))
    (boundedPowerSeriesFormalDerivativeUniformlyAbsolutelyCauchy
      C q coefficients coefficients-bounded q<1)


powerSeriesUniformlyAbsolutelyCauchyAt : ∀ coefficients radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius coefficients radius →
  ∀ point →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients (fst point))
powerSeriesUniformlyAbsolutelyCauchyAt coefficients radius uniform =
  uniformlyAbsolutelyCauchySeriesAt
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius) uniform


powerSeriesUniformlyCauchyAt : ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients radius →
  ∀ point → IsCauchySeries
    (powerSeriesTerms coefficients (fst point))
powerSeriesUniformlyCauchyAt coefficients radius uniform =
  uniformlyCauchySeriesAt
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius) uniform


powerSeriesUniformValueOnClosedRadius : ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients radius →
  ClosedAbsRadius radius → Real.ℝ
powerSeriesUniformValueOnClosedRadius coefficients radius uniform =
  uniformSeriesValue
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius) uniform


-- Keep the defining convergence rule available without forcing clients to
-- unfold the canonical evaluator and its (potentially very large) uniform
-- Cauchy proof.  This small interface matters for concrete transcendental
-- series, where proof-irrelevant convergence witnesses can otherwise cause
-- expensive normalization merely to recover the evident `HasSum` fact.

powerSeriesUniformValueOnClosedRadiusHasSum :
  ∀ coefficients radius
    (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius)
    (point : ClosedAbsRadius radius) →
  HasSum
    (powerSeriesTerms coefficients (fst point))
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform point)
powerSeriesUniformValueOnClosedRadiusHasSum
  coefficients radius uniform point =
  seriesSumHasSum
    (powerSeriesTerms coefficients (fst point))
    (uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius coefficients radius)
      uniform point)


-- The evaluator is mathematically independent of its proof argument.  Keep
-- this path opaque: concrete convergence proofs (factorial and Mertens
-- majorants in particular) can be enormous, and normalizing a `cong` through
-- them merely to change proof indices is both unnecessary and expensive.

opaque
  powerSeriesUniformValueOnClosedRadiusProofIndependent :
    ∀ coefficients radius
      (left right :
        PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
    powerSeriesUniformValueOnClosedRadius coefficients radius left
      ≡
    powerSeriesUniformValueOnClosedRadius coefficients radius right
  powerSeriesUniformValueOnClosedRadiusProofIndependent
    coefficients radius left right =
    cong
      (powerSeriesUniformValueOnClosedRadius coefficients radius)
      (isPropUniformlyCauchySeries
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius coefficients radius)
        left right)


PowerSeriesUniformlyConvergesOnRadius :
  (coefficients : RealSequence) (radius : Real.ℝ) →
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  Type₀
PowerSeriesUniformlyConvergesOnRadius coefficients radius uniform =
  UniformlyConvergesSeries
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)


powerSeriesUniformPartialSumsConverge : ∀ coefficients radius
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  PowerSeriesUniformlyConvergesOnRadius coefficients radius uniform
powerSeriesUniformPartialSumsConverge coefficients radius uniform =
  uniformPartialSumsConvergeToSeriesValue
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius) uniform


private
  constantOnClosedRadiusIsContinuous : ∀ radius coefficient →
    isContinuous
      (snd (ClosedAbsRadiusPremetricSpace radius))
      (λ _ → coefficient)
      (snd Real.ℝPremetricSpace)
  constantOnClosedRadiusIsContinuous radius coefficient point
    .IsContinuousAt.pres≈ ε =
    ∣ ε , (λ _ _ → Real.Base.isRefl≈ᶜ coefficient ε) ∣₁


  powerOnClosedRadiusIsContinuous : ∀ radius n →
    isContinuous
      (snd (ClosedAbsRadiusPremetricSpace radius))
      (λ point → fst point ^ⁿ n)
      (snd Real.ℝPremetricSpace)
  powerOnClosedRadiusIsContinuous radius n point
    .IsContinuousAt.pres≈ ε =
    PT.map
      (λ (δ , near) →
        δ , λ other point≈other → near (fst other) point≈other)
      (powIsContinuous n (fst point) .IsContinuousAt.pres≈ ε)


powerSeriesTermOnClosedRadiusIsContinuous : ∀ coefficients radius n →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (λ point →
      powerSeriesTermsOnClosedRadius coefficients radius point n)
    (snd Real.ℝPremetricSpace)
powerSeriesTermOnClosedRadiusIsContinuous coefficients radius n =
  mulOfContinuousIsContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (λ _ → coefficients n)
    (λ point → fst point ^ⁿ n)
    (constantOnClosedRadiusIsContinuous radius (coefficients n))
    (powerOnClosedRadiusIsContinuous radius n)


powerSeriesUniformValueOnClosedRadiusIsContinuous :
  ∀ coefficients radius
  (uniform : PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (powerSeriesUniformValueOnClosedRadius coefficients radius uniform)
    (snd Real.ℝPremetricSpace)
powerSeriesUniformValueOnClosedRadiusIsContinuous
  coefficients radius uniform =
  uniformSeriesValueIsContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (powerSeriesTermsOnClosedRadius coefficients radius) uniform
    (powerSeriesTermOnClosedRadiusIsContinuous coefficients radius)
