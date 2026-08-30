module Cubical.Analysis.Real.Series.PowerSeries.Entire.HigherDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ; suc)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Real.Calculus.Derivative.Base


-- Evidence is indexed by the chosen closed radius before it is packaged as
-- an entire family.  This keeps every modulus-producing input explicit.
RepeatedFormalDerivativesUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type₀
RepeatedFormalDerivativesUniformlyCauchyOnRadius
    coefficients radius =
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (repeatedFormalDerivative order coefficients) radius


RepeatedFormalDerivativeDifferenceFactorsUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type₀
RepeatedFormalDerivativeDifferenceFactorsUniformlyCauchyOnRadius
    coefficients radius =
  ∀ order →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    (repeatedFormalDerivative order coefficients) radius


EntireRepeatedFormalDerivativesUniformlyCauchy :
  RealSequence → Type₀
EntireRepeatedFormalDerivativesUniformlyCauchy coefficients =
  ∀ radius →
  RepeatedFormalDerivativesUniformlyCauchyOnRadius
    coefficients radius


EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy :
  RealSequence → Type₀
EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
    coefficients =
  ∀ radius →
  RepeatedFormalDerivativeDifferenceFactorsUniformlyCauchyOnRadius
    coefficients radius


-- This orientation is the one needed when a theorem produces the formal
-- derivative of D^k and its consumer expects D^(k+1).
formalDerivative-repeatedFormalDerivative : ∀ order coefficients →
  formalDerivative (repeatedFormalDerivative order coefficients)
    ≡ repeatedFormalDerivative (suc order) coefficients
formalDerivative-repeatedFormalDerivative order coefficients =
  sym (repeatedFormalDerivative-successor order coefficients)


entireRepeatedFormalDerivativeUniform : ∀ coefficients →
  EntireRepeatedFormalDerivativesUniformlyCauchy coefficients →
  ∀ order →
  EntirePowerSeriesUniformlyCauchy
    (repeatedFormalDerivative order coefficients)
entireRepeatedFormalDerivativeUniform
    coefficients uniform order radius =
  uniform radius order


entireRepeatedFormalDerivativeSuccessorUniform : ∀ coefficients →
  EntireRepeatedFormalDerivativesUniformlyCauchy coefficients →
  ∀ order →
  EntireFormalDerivativePowerSeriesUniformlyCauchy
    (repeatedFormalDerivative order coefficients)
entireRepeatedFormalDerivativeSuccessorUniform
    coefficients uniform order radius =
  uniform radius (suc order)


entireRepeatedFormalDerivativeFactorUniform : ∀ coefficients →
  EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
    coefficients →
  ∀ order →
  EntirePowerSeriesDifferenceFactorUniformlyCauchy
    (repeatedFormalDerivative order coefficients)
entireRepeatedFormalDerivativeFactorUniform
    coefficients factors order radius =
  factors radius order


entireHigherDerivativeValue : ∀ coefficients →
  EntireRepeatedFormalDerivativesUniformlyCauchy coefficients →
  ℕ → ℝ → ℝ
entireHigherDerivativeValue coefficients uniform order =
  entirePowerSeriesValue
    (repeatedFormalDerivative order coefficients)
    (entireRepeatedFormalDerivativeUniform
      coefficients uniform order)


entireHigherDerivativeValueIndependent :
  ∀ coefficients
    (first second :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    order x →
  entireHigherDerivativeValue coefficients first order x
    ≡ entireHigherDerivativeValue coefficients second order x
entireHigherDerivativeValueIndependent
    coefficients first second order x =
  entirePowerSeriesValueIndependent
    (repeatedFormalDerivative order coefficients)
    (entireRepeatedFormalDerivativeUniform
      coefficients first order)
    (entireRepeatedFormalDerivativeUniform
      coefficients second order)
    x


-- The local successor value uses the same radiuswise witness that enters the
-- derivative theorem.  Its agreement with the proof-independent entire
-- value is stated separately below.
entireHigherDerivativeLocalSuccessorValueAtRadius :
  ∀ coefficients
    (uniform :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    order radius x →
  absℝ x <ℝ radius → ℝ
entireHigherDerivativeLocalSuccessorValueAtRadius
    coefficients uniform order radius x interior =
  entireFormalDerivativeValueAtRadius
    (repeatedFormalDerivative order coefficients)
    (entireRepeatedFormalDerivativeSuccessorUniform
      coefficients uniform order)
    radius x interior


entireHigherDerivativeLocalSuccessorValueAtRadius-agrees :
  ∀ coefficients
    (uniform :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    order radius x
    (interior : absℝ x <ℝ radius) →
  entireHigherDerivativeValue
      coefficients uniform (suc order) x
    ≡
  entireHigherDerivativeLocalSuccessorValueAtRadius
    coefficients uniform order radius x interior
entireHigherDerivativeLocalSuccessorValueAtRadius-agrees
    coefficients uniform order radius x interior =
  entireFormalDerivativeValueAtRadius-agrees
    (repeatedFormalDerivative order coefficients)
    (entireRepeatedFormalDerivativeSuccessorUniform
      coefficients uniform order)
    radius x interior


entireHigherDerivativeValueHasSuccessorAtRadius :
  ∀ coefficients
    (uniform :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    (factors :
      EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
        coefficients)
    order radius x
    (interior : absℝ x <ℝ radius) →
  IsDerivativeAt
    (entireHigherDerivativeValue coefficients uniform order)
    (entireHigherDerivativeLocalSuccessorValueAtRadius
      coefficients uniform order radius x interior)
    x
entireHigherDerivativeValueHasSuccessorAtRadius
    coefficients uniform factors order radius x interior =
  entirePowerSeriesValueHasFormalDerivativeAtRadius
    (repeatedFormalDerivative order coefficients)
    (entireRepeatedFormalDerivativeUniform
      coefficients uniform order)
    (entireRepeatedFormalDerivativeSuccessorUniform
      coefficients uniform order)
    (entireRepeatedFormalDerivativeFactorUniform
      coefficients factors order)
    radius x interior


-- Keep the equality and derivative proof paired rather than transporting the
-- canonical value into IsDerivativeAt.  The latter causes large dependent
-- normalization in the underlying uniform-series witnesses.
entireHigherDerivativeValueSuccessorAtRadius :
  ∀ coefficients
    (uniform :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    (factors :
      EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
        coefficients)
    order radius x
    (interior : absℝ x <ℝ radius) →
  let local-successor =
        entireHigherDerivativeLocalSuccessorValueAtRadius
          coefficients uniform order radius x interior
  in
  (entireHigherDerivativeValue
      coefficients uniform (suc order) x
      ≡ local-successor)
  ×
  IsDerivativeAt
    (entireHigherDerivativeValue coefficients uniform order)
    local-successor x
entireHigherDerivativeValueSuccessorAtRadius
    coefficients uniform factors order radius x interior =
  entireHigherDerivativeLocalSuccessorValueAtRadius-agrees
    coefficients uniform order radius x interior
  , entireHigherDerivativeValueHasSuccessorAtRadius
      coefficients uniform factors order radius x interior


entireHigherDerivativeValueSuccessorAtCanonicalRadius :
  ∀ coefficients
    (uniform :
      EntireRepeatedFormalDerivativesUniformlyCauchy coefficients)
    (factors :
      EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
        coefficients)
    order x →
  let radius = entireRadiusAt x
      interior = entireRadiusAt-interior x
      local-successor =
        entireHigherDerivativeLocalSuccessorValueAtRadius
          coefficients uniform order radius x interior
  in
  (entireHigherDerivativeValue
      coefficients uniform (suc order) x
      ≡ local-successor)
  ×
  IsDerivativeAt
    (entireHigherDerivativeValue coefficients uniform order)
    local-successor x
entireHigherDerivativeValueSuccessorAtCanonicalRadius
    coefficients uniform factors order x =
  entireHigherDerivativeValueSuccessorAtRadius
    coefficients uniform factors order
    (entireRadiusAt x) x (entireRadiusAt-interior x)
