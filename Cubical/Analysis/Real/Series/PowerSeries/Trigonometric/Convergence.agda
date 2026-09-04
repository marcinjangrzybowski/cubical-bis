module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients


private
  module ℚStr = OrderedCommRingStr (snd ℚOrderedCommRing)
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


-- Both masks have absolute value at most one.  The mutual proof follows the
-- same four-cycle as the definitions and does not need a parity decision.

mutual
  sineRationalSign-abs≤one : ∀ n →
    ℚOrder.abs (sineRationalSign n) ℚ.≤ 1
  sineRationalSign-abs≤one zero =
    subst
      (λ x → x ℚ.≤ 1)
      (sym
        (ℚOrder.0≤→abs≡id 0 (ℚ.isRefl≤ 0)))
      ℚOrder.0≤1
  sineRationalSign-abs≤one (suc n) =
    cosineRationalSign-abs≤one n

  cosineRationalSign-abs≤one : ∀ n →
    ℚOrder.abs (cosineRationalSign n) ℚ.≤ 1
  cosineRationalSign-abs≤one zero =
    subst
      (λ x → x ℚ.≤ 1)
      (sym
        (ℚOrder.0≤→abs≡id 1 ℚOrder.0≤1))
      (ℚ.isRefl≤ 1)
  cosineRationalSign-abs≤one (suc n) =
    subst
      (λ x → x ℚ.≤ 1)
      (ℚ.-abs (sineRationalSign n))
      (sineRationalSign-abs≤one n)


private
  rationalSignCoefficientsMajorizedByExponential :
    ∀ (sign : ℕ → ℚ) →
    (∀ n → ℚOrder.abs (sign n) ℚ.≤ 1) →
    CoefficientMajorizedBy
      (λ n →
        rat (sign n ℚ.· exponentialRationalCoefficient n))
      exponentialCoefficients
  rationalSignCoefficientsMajorizedByExponential
      sign sign-abs≤one n =
    subst
      (_≤ℝ exponentialCoefficients n)
      (sym
        (abs-rat
          (sign n ℚ.· exponentialRationalCoefficient n)))
      (invEq
        (rat≤rat≃
          (ℚOrder.abs
            (sign n ℚ.· exponentialRationalCoefficient n))
          (exponentialRationalCoefficient n))
        rational-bound)
    where
    coefficient = exponentialRationalCoefficient n

    coefficient-abs-path : ℚOrder.abs coefficient ≡ coefficient
    coefficient-abs-path =
      ℚOrder.0≤→abs≡id
        coefficient
        (ℚ.<Weaken≤ 0 coefficient
          (snd (exponentialRationalFactorial n ℚInv.⁻¹₊)))

    rational-bound :
      ℚOrder.abs (sign n ℚ.· coefficient) ℚ.≤ coefficient
    rational-bound =
      subst2 ℚ._≤_
        (ℚ.abs·abs (sign n) coefficient)
        (ℚ.·IdL (ℚOrder.abs coefficient) ∙ coefficient-abs-path)
        (ℚStr.·MonoR≤
          (ℚOrder.abs (sign n)) 1 (ℚOrder.abs coefficient)
          (ℚOrder.0≤abs coefficient)
          (sign-abs≤one n))


sineCoefficientsMajorizedByExponential :
  CoefficientMajorizedBy sineCoefficients exponentialCoefficients
sineCoefficientsMajorizedByExponential =
  rationalSignCoefficientsMajorizedByExponential
    sineRationalSign sineRationalSign-abs≤one


cosineCoefficientsMajorizedByExponential :
  CoefficientMajorizedBy cosineCoefficients exponentialCoefficients
cosineCoefficientsMajorizedByExponential =
  rationalSignCoefficientsMajorizedByExponential
    cosineRationalSign cosineRationalSign-abs≤one


-- A uniformly Cauchy family remains uniformly Cauchy under pointwise
-- domination.  Its chosen modulus is reused at every parameter.

private
  uniformlyDominatedByUniformSeriesIsUniformlyCauchy :
    ∀ {ℓ} {A : Type ℓ}
      (terms bound : A → RealSequence) →
    (∀ point n → absℝ (terms point n) ≤ℝ bound point n) →
    UniformlyCauchySeries A bound →
    UniformlyCauchySeries A terms
  uniformlyDominatedByUniformSeriesIsUniformlyCauchy
      terms bound dominates =
    PT.map λ where
      (modulus , close) →
        modulus
        , λ point ε m n modulus≤m modulus≤n →
            snd
              (dominatedChosenCauchySeriesIsChosenCauchy
                (terms point) (bound point) (dominates point)
                (modulus , close point))
              ε m n modulus≤m modulus≤n


  closedAbsRadiusAbsolute : ∀ radius →
    ClosedAbsRadius radius → ClosedAbsRadius radius
  closedAbsRadiusAbsolute radius point =
    absℝ (fst point)
    , subst
        (_≤ℝ radius)
        (sym (absIdem (fst point)))
        (snd point)


  exponentialAtAbsoluteUniformlyCauchy : ∀ radius →
    UniformlyCauchySeries
      (ClosedAbsRadius radius)
      (λ point →
        powerSeriesTerms exponentialCoefficients
          (absℝ (fst point)))
  exponentialAtAbsoluteUniformlyCauchy radius =
    uniformlyCauchySeriesPrecompose
      (powerSeriesTermsOnClosedRadius
        exponentialCoefficients radius)
      (closedAbsRadiusAbsolute radius)
      (exponentialPowerSeriesEntireUniformlyCauchy radius)


  powerSeriesEntireUniformlyCauchyByExponentialMajorant :
    ∀ coefficients →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    EntirePowerSeriesUniformlyCauchy coefficients
  powerSeriesEntireUniformlyCauchyByExponentialMajorant
      coefficients majorized radius =
    uniformlyDominatedByUniformSeriesIsUniformlyCauchy
      (powerSeriesTermsOnClosedRadius coefficients radius)
      (λ point →
        powerSeriesTerms exponentialCoefficients
          (absℝ (fst point)))
      (λ point →
        powerSeriesTermAbsBoundByCoefficientMajorant
          coefficients exponentialCoefficients
          (fst point) (absℝ (fst point))
          majorized (≤ℝ-refl (absℝ (fst point))))
      (exponentialAtAbsoluteUniformlyCauchy radius)


entirePowerSeriesUniformlyCauchyByExponentialMajorant :
  ∀ coefficients →
  CoefficientMajorizedBy coefficients exponentialCoefficients →
  EntirePowerSeriesUniformlyCauchy coefficients
entirePowerSeriesUniformlyCauchyByExponentialMajorant =
  powerSeriesEntireUniformlyCauchyByExponentialMajorant


sinePowerSeriesEntireUniformlyCauchy :
  EntirePowerSeriesUniformlyCauchy sineCoefficients
sinePowerSeriesEntireUniformlyCauchy =
  powerSeriesEntireUniformlyCauchyByExponentialMajorant
    sineCoefficients sineCoefficientsMajorizedByExponential


cosinePowerSeriesEntireUniformlyCauchy :
  EntirePowerSeriesUniformlyCauchy cosineCoefficients
cosinePowerSeriesEntireUniformlyCauchy =
  powerSeriesEntireUniformlyCauchyByExponentialMajorant
    cosineCoefficients cosineCoefficientsMajorizedByExponential


private
  exponentialFormalDerivativeMajorant-fixed :
    formalDerivativeMajorant exponentialCoefficients
      ≡ exponentialCoefficients
  exponentialFormalDerivativeMajorant-fixed =
    funExt exponentialCoefficients-suc


  formalDerivativeMajorizedByExponential : ∀ coefficients →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    CoefficientMajorizedBy
      (formalDerivative coefficients) exponentialCoefficients
  formalDerivativeMajorizedByExponential coefficients majorized =
    subst
      (CoefficientMajorizedBy (formalDerivative coefficients))
      exponentialFormalDerivativeMajorant-fixed
      (formalDerivativePresCoefficientMajorant
        coefficients exponentialCoefficients majorized)


formalDerivativePresExponentialMajorant : ∀ coefficients →
  CoefficientMajorizedBy coefficients exponentialCoefficients →
  CoefficientMajorizedBy
    (formalDerivative coefficients) exponentialCoefficients
formalDerivativePresExponentialMajorant =
  formalDerivativeMajorizedByExponential


sineFormalDerivativePowerSeriesEntireUniformlyCauchy :
  EntireFormalDerivativePowerSeriesUniformlyCauchy sineCoefficients
sineFormalDerivativePowerSeriesEntireUniformlyCauchy =
  powerSeriesEntireUniformlyCauchyByExponentialMajorant
    (formalDerivative sineCoefficients)
    (formalDerivativeMajorizedByExponential
      sineCoefficients sineCoefficientsMajorizedByExponential)


cosineFormalDerivativePowerSeriesEntireUniformlyCauchy :
  EntireFormalDerivativePowerSeriesUniformlyCauchy cosineCoefficients
cosineFormalDerivativePowerSeriesEntireUniformlyCauchy =
  powerSeriesEntireUniformlyCauchyByExponentialMajorant
    (formalDerivative cosineCoefficients)
    (formalDerivativeMajorizedByExponential
      cosineCoefficients cosineCoefficientsMajorizedByExponential)


private
  closedAbsRadiusPairBoundary : ∀ radius →
    ClosedAbsRadiusPair radius → ClosedAbsRadius radius
  closedAbsRadiusPairBoundary radius point =
    radius
    , subst
        (_≤ℝ radius)
        (sym (absOfNonnegative radius radius-nonnegative))
        (≤ℝ-refl radius)
    where
    radius-nonnegative : 0ℝ ≤ℝ radius
    radius-nonnegative =
      ≤ℝ-trans
        0ℝ
        (absℝ (closedAbsRadiusPairLeft radius point))
        radius
        (absNonnegative
          (closedAbsRadiusPairLeft radius point))
        (snd (fst point))


  exponentialAtPairBoundaryUniformlyCauchy : ∀ radius →
    UniformlyCauchySeries
      (ClosedAbsRadiusPair radius)
      (λ _ → powerSeriesTerms exponentialCoefficients radius)
  exponentialAtPairBoundaryUniformlyCauchy radius =
    uniformlyCauchySeriesPrecompose
      (powerSeriesTermsOnClosedRadius
        exponentialCoefficients radius)
      (closedAbsRadiusPairBoundary radius)
      (exponentialPowerSeriesEntireUniformlyCauchy radius)


  differenceFactorEntireUniformlyCauchyByExponentialMajorant :
    ∀ coefficients →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients
  differenceFactorEntireUniformlyCauchyByExponentialMajorant
      coefficients majorized radius =
    uniformlyDominatedByUniformSeriesIsUniformlyCauchy
      (powerSeriesDifferenceFactorOnClosedRadius coefficients radius)
      (λ _ → powerSeriesTerms exponentialCoefficients radius)
      dominates
      (exponentialAtPairBoundaryUniformlyCauchy radius)
    where
    dominates : ∀ point n →
      absℝ
        (powerSeriesDifferenceFactorOnClosedRadius
          coefficients radius point n)
        ≤ℝ
      powerSeriesTerms exponentialCoefficients radius n
    dominates point n =
      subst
        (absℝ
          (powerSeriesDifferenceFactorOnClosedRadius
            coefficients radius point n) ≤ℝ_)
        (cong
          (λ bound → powerSeriesTerms bound radius n)
          exponentialFormalDerivativeMajorant-fixed)
        (powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
          coefficients exponentialCoefficients
          (closedAbsRadiusPairLeft radius point)
          (closedAbsRadiusPairRight radius point)
          radius majorized radius-nonnegative
          (snd (fst point)) (snd (snd point)) n)
      where
      radius-nonnegative : 0ℝ ≤ℝ radius
      radius-nonnegative =
        ≤ℝ-trans
          0ℝ
          (absℝ (closedAbsRadiusPairLeft radius point))
          radius
          (absNonnegative
            (closedAbsRadiusPairLeft radius point))
          (snd (fst point))


entireDifferenceFactorUniformlyCauchyByExponentialMajorant :
  ∀ coefficients →
  CoefficientMajorizedBy coefficients exponentialCoefficients →
  EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients
entireDifferenceFactorUniformlyCauchyByExponentialMajorant =
  differenceFactorEntireUniformlyCauchyByExponentialMajorant


sinePowerSeriesDifferenceFactorEntireUniformlyCauchy :
  EntirePowerSeriesDifferenceFactorUniformlyCauchy sineCoefficients
sinePowerSeriesDifferenceFactorEntireUniformlyCauchy =
  differenceFactorEntireUniformlyCauchyByExponentialMajorant
    sineCoefficients sineCoefficientsMajorizedByExponential


cosinePowerSeriesDifferenceFactorEntireUniformlyCauchy :
  EntirePowerSeriesDifferenceFactorUniformlyCauchy cosineCoefficients
cosinePowerSeriesDifferenceFactorEntireUniformlyCauchy =
  differenceFactorEntireUniformlyCauchyByExponentialMajorant
    cosineCoefficients cosineCoefficientsMajorizedByExponential
