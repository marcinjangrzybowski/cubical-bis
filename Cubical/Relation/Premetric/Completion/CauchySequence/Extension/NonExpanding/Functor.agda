open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding.Functor
  {ℓM ℓM' ℓN ℓN' ℓO ℓO'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (O' : PremetricSpace ℓO ℓO') where

open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  as NonExpandingDefinition

module MM = NonExpandingDefinition M' M'
module MN = NonExpandingDefinition M' N'
module NO = NonExpandingDefinition N' O'
module MO = NonExpandingDefinition M' O'


liftNonExpanding-id : MM.liftNonExpanding idⁿ ≡ idⁿ
liftNonExpanding-id =
  MM.nonExpandingExtensionality
    (MM.liftNonExpanding idⁿ) idⁿ refl

liftNonExpanding-∘ :
  ∀ (g : NE[ N' , O' ]) (f : NE[ M' , N' ]) →
  MO.liftNonExpanding (g ∘NE f) ≡
    NO.liftNonExpanding g ∘NE MN.liftNonExpanding f
liftNonExpanding-∘ g f =
  MO.nonExpandingExtensionality
    (MO.liftNonExpanding (g ∘NE f))
    (NO.liftNonExpanding g ∘NE MN.liftNonExpanding f)
    refl
