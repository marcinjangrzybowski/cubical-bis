open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Comparison
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

import Cubical.Relation.Premetric.Completion.CauchySequence.Comparison.Regular
  as RegularDefinition

module Regular = RegularDefinition M'
