open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base

module Cubical.Relation.Premetric.Completion.UniversalProperty
  {ℓM ℓM' ℓC ℓC' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (P : CompletionPresentation M' ℓC ℓC')
  (N' : PremetricSpace ℓN ℓN') where

import Cubical.Relation.Premetric.Completion.UniversalProperty.CompletionCentered
  as CompletionCenteredDefinition
import Cubical.Relation.Premetric.Completion.UniversalProperty.Extensionality
  as ExtensionalityDefinition
import Cubical.Relation.Premetric.Completion.UniversalProperty.NonExpanding
  as NonExpandingDefinition

module CompletionCentered = CompletionCenteredDefinition M' P N'
module Extensionality = ExtensionalityDefinition M' P N'
module NonExpanding = NonExpandingDefinition M' P N'
