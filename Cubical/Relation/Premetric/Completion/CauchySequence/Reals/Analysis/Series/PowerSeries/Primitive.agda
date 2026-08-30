module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Primitive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ ; fromNatℚ)
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.ScalarCompatibility
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative


successorPositiveRational : ℕ → ℚ₊
successorPositiveRational n =
  ℚ.fromNat (suc n) , ℚAbs.0<sucN n


-- Formal integration keeps the freely chosen constant term and divides the
-- coefficient of xⁿ by n+1.  Division is rational scalar multiplication, so
-- it is total on completed reals and introduces no apartness witness.

formalPrimitive : Real.ℝ → RealSequence → RealSequence
formalPrimitive constant coefficients zero = constant
formalPrimitive constant coefficients (suc n) =
  fst ((successorPositiveRational n) ⁻¹₊) Scalar.⋆ coefficients n


formalDerivative-formalPrimitive : ∀ constant coefficients →
  formalDerivative (formalPrimitive constant coefficients) ≡ coefficients
formalDerivative-formalPrimitive constant coefficients =
  funExt λ n →
    mul-rational-left-as-scalar
      (fst (successorPositiveRational n))
      (fst ((successorPositiveRational n) ⁻¹₊)
        Scalar.⋆ coefficients n)
    ∙ sym (scalar-assoc
        (fst (successorPositiveRational n))
        (fst ((successorPositiveRational n) ⁻¹₊))
        (coefficients n))
    ∙ cong (Scalar._⋆ coefficients n)
        (x·invℚ₊[x] (successorPositiveRational n))
    ∙ scalar-id (coefficients n)


formalPrimitiveDerivativeLocallyUniform :
  ∀ constant coefficients →
  LocallyUniformPowerSeries coefficients →
  LocallyUniformPowerSeries
    (formalDerivative (formalPrimitive constant coefficients))
formalPrimitiveDerivativeLocallyUniform
  constant coefficients local =
  subst LocallyUniformPowerSeries
    (sym (formalDerivative-formalPrimitive constant coefficients))
    local


-- Once the primitive itself and its divided-difference series converge
-- locally uniformly, differentiation recovers the original canonical series
-- value globally.  The coefficient identity is transported through unique
-- sums, not by unfolding either opaque Archimedean evaluator.

locallyUniformFormalPrimitiveHasDerivative :
  ∀ constant coefficients
    (local : LocallyUniformPowerSeries coefficients)
    (primitive-local :
      LocallyUniformPowerSeries
        (formalPrimitive constant coefficients)) →
  LocallyUniformPowerSeriesDifferenceFactor
    (formalPrimitive constant coefficients) →
  IsDerivative
    (locallyUniformPowerSeriesValue
      (formalPrimitive constant coefficients) primitive-local)
    (locallyUniformPowerSeriesValue coefficients local)
locallyUniformFormalPrimitiveHasDerivative
  constant coefficients local primitive-local factor-local =
  subst
    (IsDerivative
      (locallyUniformPowerSeriesValue
        (formalPrimitive constant coefficients) primitive-local))
    derivative-value≡original-value
    primitive-has-formal-derivative
  where
  derivative-local :
    LocallyUniformPowerSeries
      (formalDerivative (formalPrimitive constant coefficients))
  derivative-local =
    formalPrimitiveDerivativeLocallyUniform
      constant coefficients local

  derivative-value : Real.ℝ → Real.ℝ
  derivative-value =
    locallyUniformPowerSeriesValue
      (formalDerivative (formalPrimitive constant coefficients))
      derivative-local

  primitive-has-formal-derivative :
    IsDerivative
      (locallyUniformPowerSeriesValue
        (formalPrimitive constant coefficients) primitive-local)
      derivative-value
  primitive-has-formal-derivative =
    locallyUniformPowerSeriesHasFormalDerivative
      (formalPrimitive constant coefficients)
      primitive-local derivative-local factor-local

  derivative-value-agrees : ∀ x →
    derivative-value x ≡
    locallyUniformPowerSeriesValue coefficients local x
  derivative-value-agrees x =
    seriesSumIndependent
      (powerSeriesTerms coefficients x)
      (derivative-value x , derivative-has-original-sum)
      (locallyUniformPowerSeriesValue coefficients local x
        , locallyUniformPowerSeriesValueHasSum coefficients local x)
    where
    derivative-has-original-sum :
      HasSum (powerSeriesTerms coefficients x) (derivative-value x)
    derivative-has-original-sum =
      subst
        (λ terms → HasSum terms (derivative-value x))
        (cong (λ sequence → powerSeriesTerms sequence x)
          (formalDerivative-formalPrimitive constant coefficients))
        (locallyUniformPowerSeriesValueHasSum
          (formalDerivative (formalPrimitive constant coefficients))
          derivative-local x)

  derivative-value≡original-value :
    derivative-value ≡
    locallyUniformPowerSeriesValue coefficients local
  derivative-value≡original-value =
    funExt derivative-value-agrees
