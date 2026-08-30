open import Cubical.Relation.Premetric.Base

-- A sequence-backed completion whose Cauchy tail choice is propositionally
-- truncated independently at each positive rational radius.

module Cubical.Relation.Premetric.Completion.CauchySequence
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  M' public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  M' public

import Cubical.Relation.Premetric.Completion.CauchySequence.Approximation
  as ApproximationDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Elimination
  as EliminationDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as SequenceLimitsDefinition

module Approximation = ApproximationDefinition M'
module Elimination = EliminationDefinition M'
module SequenceLimits = SequenceLimitsDefinition M'
