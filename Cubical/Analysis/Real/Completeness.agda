module Cubical.Analysis.Real.Completeness where

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Rationals

open import Cubical.Analysis.Real.Base

import Cubical.Analysis.Completion.Completeness
  as CompletionDefinition

module Completion = CompletionDefinition ℚPremetricSpace


isCompleteℝ : PremetricTheory.isComplete ℝPremetricSpace
isCompleteℝ = Completion.isCompleteSequential
