module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit where

-- The facade preserves the original API while keeping each mathematical
-- layer independently checkable: convergence, operator bounds, integral
-- stability, preservation, and the final completion agreement.

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Sub public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.AbsBound public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Close public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Integral.PointwiseClose public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Local public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Global public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Cauchy public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Definition public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Agreement public
