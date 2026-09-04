module Cubical.Analysis.Real.Series.PowerSeries.Entire where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Interior
open import Cubical.Analysis.Real.Calculus.Derivative.Base


-- Radiuswise uniform convergence is a constructive locally uniform package
-- for an entire power series.  Keeping the radius argument explicit avoids
-- choosing neighbourhoods from truncated convergence data.

EntirePowerSeriesUniformlyCauchy : RealSequence → Type₀
EntirePowerSeriesUniformlyCauchy coefficients =
  ∀ radius → PowerSeriesUniformlyCauchyOnRadius coefficients radius


EntireFormalDerivativePowerSeriesUniformlyCauchy :
  RealSequence → Type₀
EntireFormalDerivativePowerSeriesUniformlyCauchy coefficients =
  ∀ radius →
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      coefficients radius


EntirePowerSeriesDifferenceFactorUniformlyCauchy :
  RealSequence → Type₀
EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients =
  ∀ radius →
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius


entireRadiusAt : ℝ → ℝ
entireRadiusAt x = absℝ x + 1ℝ


entireRadiusAt-interior : ∀ x →
  absℝ x <ℝ entireRadiusAt x
entireRadiusAt-interior x =
  subst2 _<ℝ_
    (addIdR (absℝ x)) refl
    (<ℝ-addL 0ℝ 1ℝ (absℝ x)
      (isOrderedCommRingℝ .IsOrderedCommRing.0<1))


entireRadiusPoint : ∀ x →
  ClosedAbsRadius (entireRadiusAt x)
entireRadiusPoint x =
  x , <ℝ-weaken
    (absℝ x) (entireRadiusAt x)
    (entireRadiusAt-interior x)


entirePowerSeriesSummableAt : ∀ coefficients →
  EntirePowerSeriesUniformlyCauchy coefficients →
  ∀ x → PowerSeriesSummableAt coefficients x
entirePowerSeriesSummableAt coefficients entire-uniform x =
  uniformlyCauchySeriesSummableAt
    (entire-uniform (entireRadiusAt x))
    (entireRadiusPoint x)


entirePowerSeriesValue : ∀ coefficients →
  EntirePowerSeriesUniformlyCauchy coefficients →
  ℝ → ℝ
entirePowerSeriesValue coefficients entire-uniform x =
  powerSeriesValue coefficients x
    (entirePowerSeriesSummableAt coefficients entire-uniform x)


entirePowerSeriesValueIndependent :
  ∀ coefficients
    (first second : EntirePowerSeriesUniformlyCauchy coefficients)
    x →
  entirePowerSeriesValue coefficients first x
    ≡ entirePowerSeriesValue coefficients second x
entirePowerSeriesValueIndependent coefficients first second x =
  seriesSumIndependent
    (powerSeriesTerms coefficients x)
    (entirePowerSeriesSummableAt coefficients first x)
    (entirePowerSeriesSummableAt coefficients second x)


-- Equal coefficients give equal values even when convergence was proved
-- independently.  Keep the witness transport inside series-sum uniqueness.
entirePowerSeriesValuePresPath : ∀ a b →
  a ≡ b →
  (a-uniform : EntirePowerSeriesUniformlyCauchy a) →
  (b-uniform : EntirePowerSeriesUniformlyCauchy b) →
  ∀ x →
  entirePowerSeriesValue a a-uniform x ≡
  entirePowerSeriesValue b b-uniform x
entirePowerSeriesValuePresPath a b a≡b a-uniform b-uniform x =
  seriesSumPresPath
    (powerSeriesTerms a x) (powerSeriesTerms b x)
    (cong (λ coefficients → powerSeriesTerms coefficients x) a≡b)
    (entirePowerSeriesSummableAt a a-uniform x)
    (entirePowerSeriesSummableAt b b-uniform x)


entirePowerSeriesValue-agreesOnClosedRadius :
  ∀ coefficients
    (entire-uniform :
      EntirePowerSeriesUniformlyCauchy coefficients)
    radius point →
  entirePowerSeriesValue coefficients entire-uniform (fst point)
    ≡
  powerSeriesUniformValueOnClosedRadius
    coefficients radius (entire-uniform radius) point
entirePowerSeriesValue-agreesOnClosedRadius
  coefficients entire-uniform radius point =
  seriesSumIndependent
    (powerSeriesTerms coefficients (fst point))
    (entirePowerSeriesSummableAt
      coefficients entire-uniform (fst point))
    ( powerSeriesUniformValueOnClosedRadius
        coefficients radius (entire-uniform radius) point
    , seriesSumHasSum
        (powerSeriesTerms coefficients (fst point))
        (uniformlyCauchySeriesSummableAt
          (entire-uniform radius) point)
    )


entireFormalDerivativeValueAtRadius :
  ∀ coefficients
    (derivative-uniform :
      EntireFormalDerivativePowerSeriesUniformlyCauchy coefficients)
    radius x →
  absℝ x <ℝ radius → ℝ
entireFormalDerivativeValueAtRadius
  coefficients derivative-uniform radius x interior =
  formalDerivativePowerSeriesUniformValueOnClosedRadius
    coefficients radius (derivative-uniform radius)
    (x , <ℝ-weaken (absℝ x) radius interior)


entireFormalDerivativeValueAtRadius-agrees :
  ∀ coefficients
    (derivative-uniform :
      EntireFormalDerivativePowerSeriesUniformlyCauchy coefficients)
    radius x
    (interior : absℝ x <ℝ radius) →
  entirePowerSeriesValue
      (formalDerivative coefficients) derivative-uniform x
    ≡
  entireFormalDerivativeValueAtRadius
    coefficients derivative-uniform radius x interior
entireFormalDerivativeValueAtRadius-agrees
  coefficients derivative-uniform radius x interior =
  entirePowerSeriesValue-agreesOnClosedRadius
    (formalDerivative coefficients) derivative-uniform radius
    (x , <ℝ-weaken (absℝ x) radius interior)


-- The derivative and its proof-independent value equality are intentionally
-- separate.  Composing the equality into this proof with `subst` forces Agda
-- to normalise the large series-sum uniqueness witness.

entirePowerSeriesValueHasFormalDerivativeAtRadius :
  ∀ coefficients
    (entire-uniform :
      EntirePowerSeriesUniformlyCauchy coefficients)
    (derivative-uniform :
      EntireFormalDerivativePowerSeriesUniformlyCauchy coefficients)
    (factor-uniform :
      EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients)
    radius x
    (interior : absℝ x <ℝ radius) →
  IsDerivativeAt
    (entirePowerSeriesValue coefficients entire-uniform)
    (entireFormalDerivativeValueAtRadius
      coefficients derivative-uniform radius x interior)
    x
entirePowerSeriesValueHasFormalDerivativeAtRadius
  coefficients entire-uniform derivative-uniform factor-uniform
  radius x interior =
  powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
    coefficients radius
    (entire-uniform radius)
    (derivative-uniform radius)
    (factor-uniform radius)
    (entirePowerSeriesValue coefficients entire-uniform)
    (entirePowerSeriesValue-agreesOnClosedRadius
      coefficients entire-uniform radius)
    x interior


entirePowerSeriesValueFormalDerivativeAtCanonicalRadius :
  ∀ coefficients
    (entire-uniform :
      EntirePowerSeriesUniformlyCauchy coefficients)
    (derivative-uniform :
      EntireFormalDerivativePowerSeriesUniformlyCauchy coefficients)
    (factor-uniform :
      EntirePowerSeriesDifferenceFactorUniformlyCauchy coefficients)
    x →
  let radius = entireRadiusAt x
      interior = entireRadiusAt-interior x
      local-derivative =
        entireFormalDerivativeValueAtRadius
          coefficients derivative-uniform radius x interior
  in
  (entirePowerSeriesValue
      (formalDerivative coefficients) derivative-uniform x
      ≡ local-derivative)
  ×
  IsDerivativeAt
    (entirePowerSeriesValue coefficients entire-uniform)
    local-derivative x
entirePowerSeriesValueFormalDerivativeAtCanonicalRadius
  coefficients entire-uniform derivative-uniform factor-uniform x =
  entireFormalDerivativeValueAtRadius-agrees
    coefficients derivative-uniform
    (entireRadiusAt x) x (entireRadiusAt-interior x)
  , entirePowerSeriesValueHasFormalDerivativeAtRadius
      coefficients entire-uniform derivative-uniform factor-uniform
      (entireRadiusAt x) x (entireRadiusAt-interior x)
