module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Calculus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Entire.HigherDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Convergence
open import Cubical.Analysis.Real.Calculus.Derivative.Base

open PositiveRationals using (ℚ₊)

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


-- Positivity turns both the absolute-value majorant and its formal
-- derivative back into the exponential coefficient sequence.  This is the
-- key fixed-point bridge between convergence and calculus.

exponentialCoefficients-abs : ∀ n →
  absℝ (exponentialCoefficients n) ≡ exponentialCoefficients n
exponentialCoefficients-abs n =
  abs-rat (exponentialRationalCoefficient n)
  ∙ cong rat
      (ℚOrder.0≤→abs≡id
        (exponentialRationalCoefficient n)
        (ℚ.<Weaken≤
          0 (exponentialRationalCoefficient n)
          (snd (exponentialRationalFactorial n ℚInv.⁻¹₊))))


exponentialCoefficients-nonnegative :
  NonnegativeCoefficients exponentialCoefficients
exponentialCoefficients-nonnegative n =
  subst
    (0ℝ ≤ℝ_)
    (exponentialCoefficients-abs n)
    (absNonnegative (exponentialCoefficients n))


exponentialCoefficients-selfMajorized :
  CoefficientMajorizedBy
    exponentialCoefficients exponentialCoefficients
exponentialCoefficients-selfMajorized =
  nonnegativeCoefficientsSelfMajorized
    exponentialCoefficients exponentialCoefficients-nonnegative


formalDerivativeMajorant-exponentialCoefficients-pointwise : ∀ n →
  formalDerivativeMajorant exponentialCoefficients n
    ≡ exponentialCoefficients n
formalDerivativeMajorant-exponentialCoefficients-pointwise n =
  exponentialCoefficients-suc n


formalDerivativeMajorant-exponentialCoefficients :
  formalDerivativeMajorant exponentialCoefficients
    ≡ exponentialCoefficients
formalDerivativeMajorant-exponentialCoefficients =
  funExt formalDerivativeMajorant-exponentialCoefficients-pointwise


-- The explicit factorial estimate already supplies this radiuswise
-- uniform witness.  The alias records its compatibility with the real
-- closed-radius calculus API.

opaque
  exponentialUniformlyCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    fst radius ℚ.< fst (exponentialPositiveNatural b) →
    PowerSeriesUniformlyCauchyOnRadius
      exponentialCoefficients (rat (fst radius))
  exponentialUniformlyCauchyWithinNaturalBound =
    exponentialPowerSeriesUniformlyCauchyWithinNaturalBound


opaque
  exponentialFormalDerivativeUniformlyCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    fst radius ℚ.< fst (exponentialPositiveNatural b) →
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      exponentialCoefficients (rat (fst radius))
  exponentialFormalDerivativeUniformlyCauchyWithinNaturalBound
      b radius radius<base =
    subst
      (λ coefficients →
        PowerSeriesUniformlyCauchyOnRadius
          coefficients (rat (fst radius)))
      (sym formalDerivative-exponentialCoefficients)
      (exponentialUniformlyCauchyWithinNaturalBound
        b radius radius<base)

private
  positiveRationalNonnegative : ∀ (radius : ℚ₊) →
    0ℝ ≤ℝ rat (fst radius)
  positiveRationalNonnegative radius =
    <ℝ-weaken 0ℝ (rat (fst radius))
      (<ℚ→<ℝ 0 (fst radius) (snd radius))

  positiveRationalBoundary : ∀ (radius : ℚ₊) →
    ClosedAbsRadius (rat (fst radius))
  positiveRationalBoundary radius =
    rat (fst radius)
    , subst
        (_≤ℝ rat (fst radius))
        (sym
          (absOfNonnegative
            (rat (fst radius))
            (positiveRationalNonnegative radius)))
        (≤ℝ-refl (rat (fst radius)))


opaque
  exponentialDerivativeMajorantIsCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b)) →
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant exponentialCoefficients)
        (rat (fst radius)))
  exponentialDerivativeMajorantIsCauchyWithinNaturalBound
      b radius radius<base =
    subst
      (λ coefficients →
        IsCauchySeries
          (powerSeriesTerms coefficients (rat (fst radius))))
      (sym formalDerivativeMajorant-exponentialCoefficients)
      (uniformlyCauchySeriesAt
        (exponentialUniformlyCauchyWithinNaturalBound
          b radius radius<base)
        (positiveRationalBoundary radius))


opaque
  exponentialDifferenceFactorUniformlyCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    fst radius ℚ.< fst (exponentialPositiveNatural b) →
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      exponentialCoefficients (rat (fst radius))
  exponentialDifferenceFactorUniformlyCauchyWithinNaturalBound
      b radius radius<base =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      exponentialCoefficients exponentialCoefficients
      (rat (fst radius))
      exponentialCoefficients-selfMajorized
      (exponentialDerivativeMajorantIsCauchyWithinNaturalBound
        b radius radius<base)


opaque
  exponentialRepeatedUniformlyCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    fst radius ℚ.< fst (exponentialPositiveNatural b) →
    RepeatedFormalDerivativesUniformlyCauchyOnRadius
      exponentialCoefficients (rat (fst radius))
  exponentialRepeatedUniformlyCauchyWithinNaturalBound
      b radius radius<base order =
    subst
      (λ coefficients →
        PowerSeriesUniformlyCauchyOnRadius
          coefficients (rat (fst radius)))
      (sym
        (repeatedFormalDerivative-exponentialCoefficients order))
      (exponentialUniformlyCauchyWithinNaturalBound
        b radius radius<base)


  exponentialRepeatedDifferenceFactorsUniformlyCauchyWithinNaturalBound :
    ∀ (b : ℕ) (radius : ℚ₊) →
    fst radius ℚ.< fst (exponentialPositiveNatural b) →
    RepeatedFormalDerivativeDifferenceFactorsUniformlyCauchyOnRadius
      exponentialCoefficients (rat (fst radius))
  exponentialRepeatedDifferenceFactorsUniformlyCauchyWithinNaturalBound
      b radius radius<base order =
    subst
      (λ coefficients →
        PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
          coefficients (rat (fst radius)))
      (sym
        (repeatedFormalDerivative-exponentialCoefficients order))
      (exponentialDifferenceFactorUniformlyCauchyWithinNaturalBound
        b radius radius<base)


exponentialClosedRadiusValueWithinNaturalBound :
  ∀ (b : ℕ) (radius : ℚ₊) →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  ClosedRationalRadius radius → ℝ
exponentialClosedRadiusValueWithinNaturalBound
    b radius radius<base =
  powerSeriesUniformValueOnClosedRadius
    exponentialCoefficients (rat (fst radius))
    (exponentialUniformlyCauchyWithinNaturalBound
      b radius radius<base)


exponentialRepeatedClosedRadiusValueWithinNaturalBound :
  ∀ (b : ℕ) (radius : ℚ₊) →
  (radius<base :
    fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  ℕ → ClosedRationalRadius radius → ℝ
exponentialRepeatedClosedRadiusValueWithinNaturalBound
    b radius radius<base order =
  powerSeriesUniformValueOnClosedRadius
    (repeatedFormalDerivative order exponentialCoefficients)
    (rat (fst radius))
    (exponentialRepeatedUniformlyCauchyWithinNaturalBound
      b radius radius<base order)


exponentialRepeatedClosedRadiusValue-fixedPoint :
  ∀ (b : ℕ) (radius : ℚ₊)
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b))
    (order : ℕ) (point : ClosedRationalRadius radius) →
  exponentialRepeatedClosedRadiusValueWithinNaturalBound
      b radius radius<base order point
    ≡
  exponentialClosedRadiusValueWithinNaturalBound
    b radius radius<base point
exponentialRepeatedClosedRadiusValue-fixedPoint
    b radius radius<base order point =
  seriesSumPresPath
    (powerSeriesTerms
      (repeatedFormalDerivative order exponentialCoefficients)
      (fst point))
    (powerSeriesTerms exponentialCoefficients (fst point))
    (cong
      (λ coefficients → powerSeriesTerms coefficients (fst point))
      (repeatedFormalDerivative-exponentialCoefficients order))
    (uniformlyCauchySeriesSummableAt
      (exponentialRepeatedUniformlyCauchyWithinNaturalBound
        b radius radius<base order)
      point)
    (uniformlyCauchySeriesSummableAt
      (exponentialUniformlyCauchyWithinNaturalBound
        b radius radius<base)
      point)


exponentialFormalDerivativeClosedRadiusValueWithinNaturalBound :
  ∀ (b : ℕ) (radius : ℚ₊) →
  (radius<base :
    fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  ClosedRationalRadius radius → ℝ
exponentialFormalDerivativeClosedRadiusValueWithinNaturalBound
    b radius radius<base =
  formalDerivativePowerSeriesUniformValueOnClosedRadius
    exponentialCoefficients (rat (fst radius))
    (exponentialFormalDerivativeUniformlyCauchyWithinNaturalBound
      b radius radius<base)


exponentialFormalDerivativeClosedRadiusValue-fixedPoint :
  ∀ (b : ℕ) (radius : ℚ₊)
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  exponentialFormalDerivativeClosedRadiusValueWithinNaturalBound
      b radius radius<base
    ≡
  exponentialClosedRadiusValueWithinNaturalBound
    b radius radius<base
exponentialFormalDerivativeClosedRadiusValue-fixedPoint
    b radius radius<base =
  funExt λ point →
    seriesSumPresPath
      (powerSeriesTerms
        (formalDerivative exponentialCoefficients) (fst point))
      (powerSeriesTerms exponentialCoefficients (fst point))
      (cong
        (λ coefficients → powerSeriesTerms coefficients (fst point))
        formalDerivative-exponentialCoefficients)
      (uniformlyCauchySeriesSummableAt
        (exponentialFormalDerivativeUniformlyCauchyWithinNaturalBound
          b radius radius<base)
        point)
      (uniformlyCauchySeriesSummableAt
        (exponentialUniformlyCauchyWithinNaturalBound
          b radius radius<base)
        point)


-- The equality and derivative proof remain paired rather than transporting
-- the fixed-point equality through IsDerivativeAlong.  This keeps the
-- proposition-valued convergence transports cheap.

exponentialClosedRadiusValueHasFixedPointDerivative :
  ∀ (b : ℕ) (radius : ℚ₊)
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  (exponentialFormalDerivativeClosedRadiusValueWithinNaturalBound
      b radius radius<base
      ≡
    exponentialClosedRadiusValueWithinNaturalBound
      b radius radius<base)
  ×
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    fst
    (exponentialClosedRadiusValueWithinNaturalBound
      b radius radius<base)
    (exponentialFormalDerivativeClosedRadiusValueWithinNaturalBound
      b radius radius<base)
exponentialClosedRadiusValueHasFixedPointDerivative
    b radius radius<base =
  exponentialFormalDerivativeClosedRadiusValue-fixedPoint
    b radius radius<base
  , powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      exponentialCoefficients (rat (fst radius))
      (exponentialUniformlyCauchyWithinNaturalBound
        b radius radius<base)
      (exponentialFormalDerivativeUniformlyCauchyWithinNaturalBound
        b radius radius<base)
      (exponentialDifferenceFactorUniformlyCauchyWithinNaturalBound
        b radius radius<base)


exponentialRepeatedSuccessorUniformlyCauchyWithinNaturalBound :
  ∀ (b : ℕ) (radius : ℚ₊) →
  (radius<base :
    fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  ∀ order →
  FormalDerivativePowerSeriesUniformlyCauchyOnRadius
    (repeatedFormalDerivative order exponentialCoefficients)
    (rat (fst radius))
exponentialRepeatedSuccessorUniformlyCauchyWithinNaturalBound
    b radius radius<base order =
  subst
    (λ coefficients →
      PowerSeriesUniformlyCauchyOnRadius
        coefficients (rat (fst radius)))
    (sym
      (formalDerivative-repeatedFormalDerivative
        order exponentialCoefficients))
    (exponentialRepeatedUniformlyCauchyWithinNaturalBound
      b radius radius<base (suc order))


exponentialRepeatedFormalDerivativeClosedRadiusValue :
  ∀ (b : ℕ) (radius : ℚ₊) →
  (radius<base :
    fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  ℕ → ClosedRationalRadius radius → ℝ
exponentialRepeatedFormalDerivativeClosedRadiusValue
    b radius radius<base order =
  formalDerivativePowerSeriesUniformValueOnClosedRadius
    (repeatedFormalDerivative order exponentialCoefficients)
    (rat (fst radius))
    (exponentialRepeatedSuccessorUniformlyCauchyWithinNaturalBound
      b radius radius<base order)


exponentialRepeatedFormalDerivativeClosedRadiusValue-fixedPoint :
  ∀ (b : ℕ) (radius : ℚ₊)
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b))
    (order : ℕ) →
  exponentialRepeatedFormalDerivativeClosedRadiusValue
      b radius radius<base order
    ≡
  exponentialClosedRadiusValueWithinNaturalBound
    b radius radius<base
exponentialRepeatedFormalDerivativeClosedRadiusValue-fixedPoint
    b radius radius<base order =
  funExt λ point →
    seriesSumPresPath
      (powerSeriesTerms
        (formalDerivative
          (repeatedFormalDerivative order exponentialCoefficients))
        (fst point))
      (powerSeriesTerms exponentialCoefficients (fst point))
      (cong
        (λ coefficients → powerSeriesTerms coefficients (fst point))
        (formalDerivative-repeatedFormalDerivative
            order exponentialCoefficients
        ∙ repeatedFormalDerivative-exponentialCoefficients
            (suc order)))
      (uniformlyCauchySeriesSummableAt
        (exponentialRepeatedSuccessorUniformlyCauchyWithinNaturalBound
          b radius radius<base order)
        point)
      (uniformlyCauchySeriesSummableAt
        (exponentialUniformlyCauchyWithinNaturalBound
          b radius radius<base)
        point)


exponentialRepeatedClosedRadiusValueHasFixedPointDerivative :
  ∀ (b : ℕ) (radius : ℚ₊)
    (radius<base :
      fst radius ℚ.< fst (exponentialPositiveNatural b))
    (order : ℕ) →
  (exponentialRepeatedFormalDerivativeClosedRadiusValue
      b radius radius<base order
      ≡
    exponentialClosedRadiusValueWithinNaturalBound
      b radius radius<base)
  ×
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    fst
    (exponentialRepeatedClosedRadiusValueWithinNaturalBound
      b radius radius<base order)
    (exponentialRepeatedFormalDerivativeClosedRadiusValue
      b radius radius<base order)
exponentialRepeatedClosedRadiusValueHasFixedPointDerivative
    b radius radius<base order =
  exponentialRepeatedFormalDerivativeClosedRadiusValue-fixedPoint
    b radius radius<base order
  , powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      (repeatedFormalDerivative order exponentialCoefficients)
      (rat (fst radius))
      (exponentialRepeatedUniformlyCauchyWithinNaturalBound
        b radius radius<base order)
      (exponentialRepeatedSuccessorUniformlyCauchyWithinNaturalBound
        b radius radius<base order)
      (exponentialRepeatedDifferenceFactorsUniformlyCauchyWithinNaturalBound
        b radius radius<base order)
