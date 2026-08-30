open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph
  as CauchyGraphDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CompletionCentered
  as CompletionCenteredDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  as NonExpandingDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.Lipschitz
  as LipschitzDefinition
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.UniversalProperty
  as UniversalPropertyDefinition
import Cubical.Relation.Premetric.Completion.UniversalProperty.Instances.CauchySequence
  as UniversalPropertiesDefinition

module CauchyGraph = CauchyGraphDefinition M' N'
module CompletionCentered = CompletionCenteredDefinition M' N'
module NonExpanding = NonExpandingDefinition M' N'
module Lipschitz = LipschitzDefinition M' N'
module UniversalProperty = UniversalPropertyDefinition M' N'
module UniversalProperties = UniversalPropertiesDefinition M' N'
