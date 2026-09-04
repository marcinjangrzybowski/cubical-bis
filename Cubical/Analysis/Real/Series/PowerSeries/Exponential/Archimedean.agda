module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order.Inductive as ℕ using (<ᵗsucm)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ℕ₊₁→ℕ)
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Convergence


-- A positive natural radius is strictly below its successor.  This is the
-- small exact-rational step which connects the Archimedean real bound to the
-- factorial majorant indexed by a natural base.
naturalRadiusBelowSuccessorBase : ∀ n →
  naturalRational n ℚ.<
    fst (exponentialPositiveNatural (ℕ₊₁→ℕ n))
naturalRadiusBelowSuccessorBase (1+ n) =
  ℚ.<ℤ→<ℚ/
    (pos (suc n)) (pos (suc (suc n))) (1+ zero)
    (ℤ.pos<pos (ℕ.<ᵗsucm {m = suc n}))


-- Restrict the rational closed-radius result to any real radius below the
-- selected natural bound.  The modulus is reused unchanged.
exponentialPowerSeriesUniformlyCauchyFromNaturalRealBound :
  ∀ radius n →
  radius <ℝ rat (naturalRational n) →
  PowerSeriesUniformlyCauchyOnRadius exponentialCoefficients radius
exponentialPowerSeriesUniformlyCauchyFromNaturalRealBound
    radius n radius<n =
  powerSeriesUniformlyCauchyOnSmallerRadius
    exponentialCoefficients radius (rat (naturalRational n))
    (<ℝ-weaken radius (rat (naturalRational n)) radius<n)
    (exponentialPowerSeriesUniformlyCauchyWithinNaturalBound
      (ℕ₊₁→ℕ n) (naturalBound n)
      (naturalRadiusBelowSuccessorBase n))


-- Archimedean elimination is into a proposition: no global natural bound is
-- selected.  Consequently the result remains constructive while providing
-- the radiuswise package expected by the generic entire-series interface.
opaque
  exponentialPowerSeriesEntireUniformlyCauchy :
    EntirePowerSeriesUniformlyCauchy exponentialCoefficients
  exponentialPowerSeriesEntireUniformlyCauchy radius =
    PT.rec
      (isPropUniformlyCauchySeries
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius exponentialCoefficients radius))
      (λ where
        (n , radius<n) →
          exponentialPowerSeriesUniformlyCauchyFromNaturalRealBound
            radius n radius<n)
      (∃naturalUpperBound radius)


exponentialPowerSeriesIsAbsolutelyCauchyFromNaturalAbsBound :
  ∀ x → NaturalAbsBound x →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsAbsolutelyCauchyFromNaturalAbsBound
    x (n , absx<n) =
  exponentialPowerSeriesIsAbsolutelyCauchyWithinNaturalBound
    (ℕ₊₁→ℕ n) (naturalBound n) x
    (<ℝ-weaken (absℝ x) (rat (naturalRational n)) absx<n)
    (naturalRadiusBelowSuccessorBase n)


opaque
  exponentialPowerSeriesIsAbsolutelyCauchyEverywhere : ∀ x →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms exponentialCoefficients x)
  exponentialPowerSeriesIsAbsolutelyCauchyEverywhere x =
    PT.rec
      (isPropIsAbsolutelyCauchySeries
        (powerSeriesTerms exponentialCoefficients x))
      (exponentialPowerSeriesIsAbsolutelyCauchyFromNaturalAbsBound x)
      (∃naturalAbsBound x)


exponentialPowerSeriesIsCauchyEverywhere : ∀ x →
  IsCauchySeries (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsCauchyEverywhere x =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyEverywhere x)


exponentialPowerSeriesSummableEverywhere : ∀ x →
  PowerSeriesSummableAt exponentialCoefficients x
exponentialPowerSeriesSummableEverywhere x =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyEverywhere x)


exponentialPowerSeriesHasSumEverywhere : ∀ x →
  HasSum (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesValue exponentialCoefficients x
      (exponentialPowerSeriesSummableEverywhere x))
exponentialPowerSeriesHasSumEverywhere x =
  seriesSumHasSum
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesSummableEverywhere x)
