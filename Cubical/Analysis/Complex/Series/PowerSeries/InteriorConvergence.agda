module Cubical.Analysis.Complex.Series.PowerSeries.InteriorConvergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.Majorant as Real
import Cubical.Analysis.Real.Series.PowerSeries.InteriorConvergence as Real
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds

-- A single native witness for the original norm-majorant at R supplies the
-- derivative-majorant witness at every specified 0 ≤ r < R. The real secant
-- comparison handles all convergence work; the complex part is reassociation.
opaque
  complexPowerSeriesDerivativeMajorantIsCauchyAtInterior : ∀ coefficients inner outer →
    0ℝ ≤ℝ inner → inner <ℝ outer →
    Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) →
    Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients inner)
  complexPowerSeriesDerivativeMajorantIsCauchyAtInterior coefficients inner outer positive strict witness =
    subst Real.IsCauchySeries (funExt λ n →
      cong (_· powℝ inner n) (mulComm (realNatural (suc n)) (normℂ (coefficients (suc n))))
      ∙ sym (mulAssoc (normℂ (coefficients (suc n))) (realNatural (suc n)) (powℝ inner n)))
      (Real.formalDerivativeMajorantIsCauchyAtInterior (λ n → normℂ (coefficients n)) inner outer
        (λ n → normℂ-nonnegative (coefficients n)) positive strict witness)
