open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

-- The canonical extension theorem is CauchyContinuous: a graph over a
-- Cauchy source sequence must have a Cauchy target sequence.  It supplies
-- construction, uniqueness, preservation of Cauchy sequences, and an
-- equivalence between restrictions and graph-compatible extensions.
--
-- CompletionCentered and UniformlyContinuous are sufficient hypotheses;
-- they reduce to CauchyContinuous and reuse that one construction.  The
-- explicit modulus calculation for uniform continuity is deliberately kept
-- one level lower in UniformlyContinuous.Technical.

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  as CompletionCenteredDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous
  as UniformlyContinuousDefinition

module CauchyContinuous = CauchyContinuousDefinition M' N'
module CompletionCentered = CompletionCenteredDefinition M' N'
module UniformlyContinuous = UniformlyContinuousDefinition M' N'
