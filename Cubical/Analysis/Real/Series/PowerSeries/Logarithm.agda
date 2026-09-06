module Cubical.Analysis.Real.Series.PowerSeries.Logarithm where

-- The choice-free local power series x + x²/2 + x³/3 + ⋯ on |x| < 1.
-- This module does not assert compatibility with a separately constructed
-- global logarithm; that requires a log/exponential identification theorem.
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Primitive public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Convergence public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.DerivativeConvergence public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Derivative public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.UniformDerivative public
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.OpenDomain public
