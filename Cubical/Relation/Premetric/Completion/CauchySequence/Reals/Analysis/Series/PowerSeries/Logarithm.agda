module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Logarithm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Int.Fast.Base as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ ; fromNatℚ)
open import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Primitive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)

  onePositiveRational : ℚ₊
  onePositiveRational = successorPositiveRational zero

  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


-- This is the power-series germ of -log(1-x):
--
--   x + x²/2 + x³/3 + ⋯ .
--
-- Defining it as the formal primitive of the geometric coefficients makes
-- the derivative identity algebraic.  Analytic convergence is then supplied
-- independently below, on every positive rational radius strictly below 1.

negativeLogOneMinusCoefficients : RealSequence
negativeLogOneMinusCoefficients =
  formalPrimitive zeroℝ unitCoefficients


formalDerivative-negativeLogOneMinus :
  formalDerivative negativeLogOneMinusCoefficients ≡ unitCoefficients
formalDerivative-negativeLogOneMinus =
  formalDerivative-formalPrimitive zeroℝ unitCoefficients


private
  one≤successorRational : ∀ n →
    ℚ.fromNat 1 ℚ.≤ ℚ.fromNat (suc n)
  one≤successorRational n =
    ≤ℤ→≤ℚ (pos 1) (pos (suc n))
      (ℤ.ℕ≤→pos-≤-pos 1 (suc n)
        (ℕ.suc-≤-suc ℕ.zero-≤))

  successorInverse≤one : ∀ n →
    fst ((successorPositiveRational n) ⁻¹₊) ℚ.≤ 1
  successorInverse≤one n =
    ℚInv.invℚ₊≤invℚ₊
      (successorPositiveRational n) onePositiveRational
      (one≤successorRational n)

  negativeLogCoefficientPath : ∀ n →
    negativeLogOneMinusCoefficients (suc n) ≡
    Real.ιℚ (fst ((successorPositiveRational n) ⁻¹₊))
  negativeLogCoefficientPath n =
    Scalar.scalar-ι
      (fst ((successorPositiveRational n) ⁻¹₊)) 1
    ∙ cong Real.ιℚ ℚ!


-- All coefficients have absolute value at most one.  Consequently the
-- standard geometric majorant gives absolute uniform convergence on closed
-- balls |x| ≤ q for every rational q < 1, as well as convergence of the
-- formal derivative and the divided-difference series used by calculus.

opaque
  negativeLogOneMinusCoefficientsBounded :
    CoefficientAbsBound onePositiveRational
      negativeLogOneMinusCoefficients
  negativeLogOneMinusCoefficientsBounded zero =
    subst (_≤ℝ oneℝ)
      (sym Abs.absℝ-zero)
      (≤ℚ→≤ℝ 0 1 (ℚAbs.0≤pos 1 (1+ zero)))
  negativeLogOneMinusCoefficientsBounded (suc n) =
    subst (_≤ℝ oneℝ)
      (sym absoluteCoefficientPath)
      (≤ℚ→≤ℝ
        (fst ((successorPositiveRational n) ⁻¹₊)) 1
        (successorInverse≤one n))
    where
    absoluteCoefficientPath :
      Abs.absℝ (negativeLogOneMinusCoefficients (suc n)) ≡
      Real.ιℚ (fst ((successorPositiveRational n) ⁻¹₊))
    absoluteCoefficientPath =
      cong Abs.absℝ (negativeLogCoefficientPath n)
      ∙ Abs.absℝ-ι (fst ((successorPositiveRational n) ⁻¹₊))
      ∙ cong Real.ιℚ
          (ℚOrder.0≤→abs≡id
            (fst ((successorPositiveRational n) ⁻¹₊))
            (ℚ.<Weaken≤
              0 (fst ((successorPositiveRational n) ⁻¹₊))
              (snd ((successorPositiveRational n) ⁻¹₊))))


opaque
  negativeLogOneMinusUniformlyAbsolutelyCauchy : ∀ (q : ℚ₊) →
    fst q ℚ.< 1 →
    PowerSeriesUniformlyAbsolutelyCauchyOnRadius
      negativeLogOneMinusCoefficients (Real.ιℚ (fst q))
  negativeLogOneMinusUniformlyAbsolutelyCauchy q q<1 =
    boundedPowerSeriesUniformlyAbsolutelyCauchy
      onePositiveRational q negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficientsBounded q<1


  negativeLogOneMinusUniformlyCauchy : ∀ (q : ℚ₊) →
    fst q ℚ.< 1 →
    PowerSeriesUniformlyCauchyOnRadius
      negativeLogOneMinusCoefficients (Real.ιℚ (fst q))
  negativeLogOneMinusUniformlyCauchy q q<1 =
    boundedPowerSeriesUniformlyCauchy
      onePositiveRational q negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficientsBounded q<1


negativeLogOneMinusOnClosedRadius :
  (q : ℚ₊) → fst q ℚ.< 1 →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
negativeLogOneMinusOnClosedRadius q q<1 =
  powerSeriesUniformValueOnClosedRadius
    negativeLogOneMinusCoefficients (Real.ιℚ (fst q))
    (negativeLogOneMinusUniformlyCauchy q q<1)


opaque
  negativeLogOneMinusFormalDerivativeUniformlyCauchy :
    ∀ (q : ℚ₊) → fst q ℚ.< 1 →
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative negativeLogOneMinusCoefficients)
      (Real.ιℚ (fst q))
  negativeLogOneMinusFormalDerivativeUniformlyCauchy q q<1 =
    boundedPowerSeriesFormalDerivativeUniformlyCauchy
      onePositiveRational q negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficientsBounded q<1


negativeLogOneMinusFormalDerivativeOnClosedRadius :
  (q : ℚ₊) → fst q ℚ.< 1 →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
negativeLogOneMinusFormalDerivativeOnClosedRadius q q<1 =
  powerSeriesUniformValueOnClosedRadius
    (formalDerivative negativeLogOneMinusCoefficients)
    (Real.ιℚ (fst q))
    (negativeLogOneMinusFormalDerivativeUniformlyCauchy q q<1)


closedSubunitRadiusPointAbs<one :
  ∀ (q : ℚ₊) → fst q ℚ.< 1 →
  (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
  Abs.absℝ (fst point) <ℝ oneℝ
closedSubunitRadiusPointAbs<one q q<1 point =
  ≤<ℝ-trans
    (Abs.absℝ (fst point)) (Real.ιℚ (fst q)) oneℝ
    (snd point) (<ℚ→<ℝ (fst q) 1 q<1)


closedSubunitRadiusPoint<one :
  ∀ (q : ℚ₊) → fst q ℚ.< 1 →
  (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
  fst point <ℝ oneℝ
closedSubunitRadiusPoint<one q q<1 point =
  ≤<ℝ-trans
    (fst point) (Abs.absℝ (fst point)) oneℝ
    (x≤abs (fst point))
    (closedSubunitRadiusPointAbs<one q q<1 point)


negativeLogOneMinusReciprocalOnClosedRadius :
  (q : ℚ₊) → (q<1 : fst q ℚ.< 1) →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
negativeLogOneMinusReciprocalOnClosedRadius q q<1 point =
  geometricReciprocal
    (fst point) (closedSubunitRadiusPoint<one q q<1 point)


-- The formal derivative is not only represented by the geometric
-- coefficients: its concrete uniform sum is the positive reciprocal of
-- 1-x.  This is stated pointwise because the positivity proof carried by
-- `positiveReciprocal` depends on the chosen closed-ball point.

negativeLogOneMinusFormalDerivativeValue≡Reciprocal :
  (q : ℚ₊) (q<1 : fst q ℚ.< 1) →
  (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
  negativeLogOneMinusFormalDerivativeOnClosedRadius q q<1 point
    ≡ negativeLogOneMinusReciprocalOnClosedRadius q q<1 point
negativeLogOneMinusFormalDerivativeValue≡Reciprocal q q<1 point =
  seriesSumIndependent derivative-terms value-summable reciprocal-summable
  where
  x : Real.ℝ
  x = fst point

  derivative-terms : RealSequence
  derivative-terms =
    powerSeriesTerms (formalDerivative negativeLogOneMinusCoefficients) x

  derivative-terms≡geometric :
    derivative-terms ≡ geometricTerms x
  derivative-terms≡geometric =
    cong
      (λ coefficients → powerSeriesTerms coefficients x)
      formalDerivative-negativeLogOneMinus
    ∙ powerSeriesTerms-unitCoefficients-sequence x

  value-summable : Summable derivative-terms
  value-summable =
    negativeLogOneMinusFormalDerivativeOnClosedRadius q q<1 point
    , powerSeriesUniformValueOnClosedRadiusHasSum
        (formalDerivative negativeLogOneMinusCoefficients)
        (Real.ιℚ (fst q))
        (negativeLogOneMinusFormalDerivativeUniformlyCauchy q q<1)
        point

  reciprocal-summable : Summable derivative-terms
  reciprocal-summable =
    negativeLogOneMinusReciprocalOnClosedRadius q q<1 point
    , subst
        (λ terms →
          HasSum terms
            (negativeLogOneMinusReciprocalOnClosedRadius q q<1 point))
        (sym derivative-terms≡geometric)
        (geometricSeriesHasSumOfAbs<1 x
          (closedSubunitRadiusPointAbs<one q q<1 point))


-- The evaluator is indexed by a proof of uniform Cauchyness, but its value is
-- not.  The opaque proof-independence interface in `Uniform` lets us expose a
-- convenient derivative theorem without normalizing the large majorant
-- witnesses hidden in the two named evaluators.

opaque
  negativeLogOneMinusHasFormalDerivativeOnClosedRadius :
    (q : ℚ₊) (q<1 : fst q ℚ.< 1) →
    IsDerivativeAlong
      (snd (ClosedAbsRadiusPremetricSpace (Real.ιℚ (fst q))))
      fst
      (negativeLogOneMinusOnClosedRadius q q<1)
      (negativeLogOneMinusFormalDerivativeOnClosedRadius q q<1)
  negativeLogOneMinusHasFormalDerivativeOnClosedRadius q q<1 =
    subst2
      (IsDerivativeAlong
        (snd (ClosedAbsRadiusPremetricSpace (Real.ιℚ (fst q)))) fst)
      original-value-path
      derivative-value-path
      (boundedPowerSeriesUniformValueHasFormalDerivative
        onePositiveRational q negativeLogOneMinusCoefficients
        negativeLogOneMinusCoefficientsBounded q<1)
    where
    original-value-path :
      powerSeriesUniformValueOnClosedRadius
          negativeLogOneMinusCoefficients (Real.ιℚ (fst q))
          (boundedPowerSeriesUniformlyCauchy
            onePositiveRational q negativeLogOneMinusCoefficients
            negativeLogOneMinusCoefficientsBounded q<1)
        ≡
      negativeLogOneMinusOnClosedRadius q q<1
    original-value-path =
      powerSeriesUniformValueOnClosedRadiusProofIndependent
        negativeLogOneMinusCoefficients (Real.ιℚ (fst q))
        (boundedPowerSeriesUniformlyCauchy
          onePositiveRational q negativeLogOneMinusCoefficients
          negativeLogOneMinusCoefficientsBounded q<1)
        (negativeLogOneMinusUniformlyCauchy q q<1)

    derivative-value-path :
      powerSeriesUniformValueOnClosedRadius
          (formalDerivative negativeLogOneMinusCoefficients)
          (Real.ιℚ (fst q))
          (boundedPowerSeriesFormalDerivativeUniformlyCauchy
            onePositiveRational q negativeLogOneMinusCoefficients
            negativeLogOneMinusCoefficientsBounded q<1)
        ≡
      negativeLogOneMinusFormalDerivativeOnClosedRadius q q<1
    derivative-value-path =
      powerSeriesUniformValueOnClosedRadiusProofIndependent
        (formalDerivative negativeLogOneMinusCoefficients)
        (Real.ιℚ (fst q))
        (boundedPowerSeriesFormalDerivativeUniformlyCauchy
          onePositiveRational q negativeLogOneMinusCoefficients
          negativeLogOneMinusCoefficientsBounded q<1)
        (negativeLogOneMinusFormalDerivativeUniformlyCauchy q q<1)
