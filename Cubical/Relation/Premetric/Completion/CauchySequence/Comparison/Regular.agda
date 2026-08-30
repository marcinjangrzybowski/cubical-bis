open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Comparison.Regular
  {ℓ ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularCompletion
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularExtension
import Cubical.Relation.Premetric.Completion.Base
  as RegularBase
import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric

module R = RegularCompletion M'
module RB = RegularBase M'
module C = CauchyCompletion M'
module CP = CompletionPremetric M'


injectionⁿ : NE[ M' , CP.CompletionPremetricSpace ]
injectionⁿ .fst = C.ι
injectionⁿ .snd .IsNonExpanding.pres≈ = C.ι-ι

module Extend = RegularExtension.LiftCompleteCodomain
  M' CP.CompletionPremetricSpace CP.isCompleteCompletion

fromRegularⁿ : NE[ R.ℭPremetricSpace , CP.CompletionPremetricSpace ]
fromRegularⁿ = Extend.liftNonExpanding injectionⁿ

fromRegular-ι : fst fromRegularⁿ ∘ RB.ι ≡ C.ι
fromRegular-ι = Extend.liftⁿ∘ι injectionⁿ
