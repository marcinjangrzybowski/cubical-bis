open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.Completeness
  {ℓM ℓM'} (M' : PremetricSpace ℓM ℓM') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularPropertiesDefinition

module SP = SequentialPropertiesDefinition M'
module Comparison = ComparisonDefinition M'
module Regular = RegularPropertiesDefinition M'


-- Completeness is invariant under the already established isometric
-- comparison.  Stating the result here keeps clients of the sequential
-- completion independent of the regular completion presentation.

toRegularⁿ : NE[
  SP.ℭ̂ₛPremetricSpace , Comparison.C.ℭPremetricSpace ]
toRegularⁿ = Comparison.toRegular ,
  isIsometry→IsNonExpanding
    (SP.ℭ̂ₛPremetricSpace .snd)
    Comparison.sequentialRegularEquiv
    (Comparison.C.ℭPremetricSpace .snd)
    Comparison.sequentialRegularIsometry

fromRegularⁿ : NE[
  Comparison.C.ℭPremetricSpace , SP.ℭ̂ₛPremetricSpace ]
fromRegularⁿ = Comparison.fromRegular ,
  isIsometry→IsNonExpanding
    (Comparison.C.ℭPremetricSpace .snd)
    Comparison.regularSequentialEquiv
    (SP.ℭ̂ₛPremetricSpace .snd)
    Comparison.regularSequentialIsometry

isCompleteSequential :
  PremetricTheory.isComplete SP.ℭ̂ₛPremetricSpace
isCompleteSequential = retractPresIsComplete
  Regular.isCompleteℭ
  toRegularⁿ fromRegularⁿ
  (Comparison.sequentialRegularIso .Iso.ret)
