open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Comparison
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Base
  as RegularDefinition
import Cubical.Relation.Premetric.Completion.Alternative
  as ExplicitScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Equivalence
  as RegularExplicitDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.Equivalence
  as SequentialComparisonDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as SequentialRegularDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularPropertiesDefinition

module Regular = RegularDefinition M'
module ExplicitScale = ExplicitScaleDefinition M'
module RegularExplicit = RegularExplicitDefinition M'
module TruncatedScale = TruncatedScaleDefinition M'
module Sequential = SequentialDefinition M'
module SequentialProperties = SequentialPropertiesDefinition M'
module SequentialComparison = SequentialComparisonDefinition M'
module SequentialRegular = SequentialRegularDefinition M'
module RegularProperties = RegularPropertiesDefinition M'


-- The four proved presentations differ only in what their limit constructor
-- stores:
--
--   Regular        a positive-rational family with the canonical scale;
--   ExplicitScale  a positive-rational family and an explicit Γ scale;
--   TruncatedScale a positive-rational family with merely a suitable scale;
--   Sequential     a natural-number sequence with merely a Cauchy modulus.
--
-- This module is the small public map of their relationships.  The sampling
-- and reindexing arguments proving the last two equivalences remain under
-- Sequential.Comparison.TruncatedScale.

regularExplicitScaleEquiv : Regular.ℭ ≃ ExplicitScale.ℭ̂
regularExplicitScaleEquiv = RegularExplicit.regularAlternativeEquiv

explicitTruncatedScaleEquiv : ExplicitScale.ℭ̂ ≃ TruncatedScale.ℭ̂ᵣ
explicitTruncatedScaleEquiv = TruncatedScale.explicitTruncatedScaleEquiv

sequentialTruncatedScaleEquiv : Sequential.ℭ̂ₛ ≃ TruncatedScale.ℭ̂ᵣ
sequentialTruncatedScaleEquiv = SequentialComparison.sequentialTruncatedScaleEquiv

sequentialExplicitScaleEquiv : Sequential.ℭ̂ₛ ≃ ExplicitScale.ℭ̂
sequentialExplicitScaleEquiv =
  SequentialComparison.sequentialExplicitScaleEquiv

sequentialRegularIso : Iso Sequential.ℭ̂ₛ Regular.ℭ
sequentialRegularIso = SequentialRegular.sequentialRegularIso

regularSequentialIso : Iso Regular.ℭ Sequential.ℭ̂ₛ
regularSequentialIso = SequentialRegular.regularSequentialIso

sequentialRegularEquiv : Sequential.ℭ̂ₛ ≃ Regular.ℭ
sequentialRegularEquiv = SequentialRegular.sequentialRegularEquiv

regularSequentialEquiv : Regular.ℭ ≃ Sequential.ℭ̂ₛ
regularSequentialEquiv = SequentialRegular.regularSequentialEquiv

sequentialRegularIsometry : IsIsometry
  (SequentialProperties.ℭ̂ₛPremetricSpace .snd)
  sequentialRegularEquiv
  (RegularProperties.ℭPremetricSpace .snd)
sequentialRegularIsometry = SequentialRegular.sequentialRegularIsometry

regularSequentialIsometry : IsIsometry
  (RegularProperties.ℭPremetricSpace .snd)
  regularSequentialEquiv
  (SequentialProperties.ℭ̂ₛPremetricSpace .snd)
regularSequentialIsometry = SequentialRegular.regularSequentialIsometry

sequentialRegularPremetricEquiv : PremetricSpaceEquiv
  SequentialProperties.ℭ̂ₛPremetricSpace
  RegularProperties.ℭPremetricSpace
sequentialRegularPremetricEquiv =
  SequentialRegular.sequentialRegularPremetricEquiv

regularSequentialPremetricEquiv : PremetricSpaceEquiv
  RegularProperties.ℭPremetricSpace
  SequentialProperties.ℭ̂ₛPremetricSpace
regularSequentialPremetricEquiv =
  SequentialRegular.regularSequentialPremetricEquiv
