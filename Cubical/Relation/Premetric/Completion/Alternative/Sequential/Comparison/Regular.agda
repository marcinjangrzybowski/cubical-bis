open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Base
  as RegularDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.To
  as ToTruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.From
  as FromTruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.Equivalence
  as SequentialExplicitScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularClosenessDefinition

module Regular = RegularDefinition M'
module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = ToTruncatedScaleDefinition M'
module F = FromTruncatedScaleDefinition M'
module SE = SequentialExplicitScaleDefinition M'
module R = TruncatedScaleDefinition M'
module A = AlternativeDefinition M'
module C = RegularClosenessDefinition M'

private
  M = M' .fst
  module PM = PremetricStr (M' .snd)
  module RegularPremetric = PremetricStr (C.ℭPremetricSpace .snd)


-- The direct comparison with Completion.Base.  Its underlying maps are the
-- composites through the explicit-scale presentation, but users of this
-- module need not mention either intermediate completion.

sequentialRegularIso : Iso S.ℭ̂ₛ Regular.ℭ
sequentialRegularIso =
  compIso SE.sequentialExplicitScaleIso
    (invIso A.regularAlternativeIso)

regularSequentialIso : Iso Regular.ℭ S.ℭ̂ₛ
regularSequentialIso = invIso sequentialRegularIso

sequentialRegularEquiv : S.ℭ̂ₛ ≃ Regular.ℭ
sequentialRegularEquiv = isoToEquiv sequentialRegularIso

regularSequentialEquiv : Regular.ℭ ≃ S.ℭ̂ₛ
regularSequentialEquiv = isoToEquiv regularSequentialIso

toRegular : S.ℭ̂ₛ → Regular.ℭ
toRegular = sequentialRegularIso .Iso.fun

fromRegular : Regular.ℭ → S.ℭ̂ₛ
fromRegular = sequentialRegularIso .Iso.inv

toRegular∼ : ∀ x y ε →
  x S.∼̂ₛ[ ε ] y →
  toRegular x Regular.∼[ ε ] toRegular y
toRegular∼ x y ε p =
  A.←̂~ _ _ ε
    (R.toExplicitScale∼ _ _ ε (T.toTruncatedScale∼ x y ε p))

-- The inverse recursion preserves a relation with any strictly larger
-- radius.  Roundedness of the regular completion supplies the smaller
-- radius needed to obtain exact preservation here.

fromRegular∼ : ∀ x y ε →
  x Regular.∼[ ε ] y →
  fromRegular x S.∼̂ₛ[ ε ] fromRegular y
fromRegular∼ x y ε p =
  PT.rec (S.isProp∼ (fromRegular x) ε (fromRegular y))
    (λ { (δ , δ<ε , q) →
      F.fromTruncatedScaleSlack
        (R.→ᵣ (A.→̂ x)) (R.→ᵣ (A.→̂ y)) δ
        (R.∼→ᵣ (A.→̂ x) (A.→̂ y) δ
          (A.→̂~ x y δ q))
        ε δ<ε })
    (RegularPremetric.isRounded≈ x y ε p)

toRegular-reflects∼ : ∀ x y ε →
  toRegular x Regular.∼[ ε ] toRegular y →
  x S.∼̂ₛ[ ε ] y
toRegular-reflects∼ x y ε p =
  subst2 (λ u v → u S.∼̂ₛ[ ε ] v)
    (sequentialRegularIso .Iso.ret x)
    (sequentialRegularIso .Iso.ret y)
    (fromRegular∼ (toRegular x) (toRegular y) ε p)

fromRegular-reflects∼ : ∀ x y ε →
  fromRegular x S.∼̂ₛ[ ε ] fromRegular y →
  x Regular.∼[ ε ] y
fromRegular-reflects∼ x y ε p =
  subst2 (λ u v → u Regular.∼[ ε ] v)
    (sequentialRegularIso .Iso.sec x)
    (sequentialRegularIso .Iso.sec y)
    (toRegular∼ (fromRegular x) (fromRegular y) ε p)

toRegular-closenessEquiv : ∀ x y ε →
  (x S.∼̂ₛ[ ε ] y) ≃
  (toRegular x Regular.∼[ ε ] toRegular y)
toRegular-closenessEquiv x y ε = propBiimpl→Equiv
  (S.isProp∼ x ε y)
  (RegularPremetric.isProp≈ (toRegular x) (toRegular y) ε)
  (toRegular∼ x y ε)
  (toRegular-reflects∼ x y ε)

fromRegular-closenessEquiv : ∀ x y ε →
  (x Regular.∼[ ε ] y) ≃
  (fromRegular x S.∼̂ₛ[ ε ] fromRegular y)
fromRegular-closenessEquiv x y ε = propBiimpl→Equiv
  (RegularPremetric.isProp≈ x y ε)
  (S.isProp∼ (fromRegular x) ε (fromRegular y))
  (fromRegular∼ x y ε)
  (fromRegular-reflects∼ x y ε)


sequentialRegularIsometry : IsIsometry
  (SP.ℭ̂ₛPremetricSpace .snd)
  sequentialRegularEquiv
  (C.ℭPremetricSpace .snd)
sequentialRegularIsometry .IsIsometry.pres≈ x ε y =
  toRegular-closenessEquiv x y ε

regularSequentialIsometry : IsIsometry
  (C.ℭPremetricSpace .snd)
  regularSequentialEquiv
  (SP.ℭ̂ₛPremetricSpace .snd)
regularSequentialIsometry .IsIsometry.pres≈ x ε y =
  fromRegular-closenessEquiv x y ε

sequentialRegularPremetricEquiv :
  PremetricSpaceEquiv SP.ℭ̂ₛPremetricSpace C.ℭPremetricSpace
sequentialRegularPremetricEquiv =
  sequentialRegularEquiv , sequentialRegularIsometry

regularSequentialPremetricEquiv :
  PremetricSpaceEquiv C.ℭPremetricSpace SP.ℭ̂ₛPremetricSpace
regularSequentialPremetricEquiv =
  regularSequentialEquiv , regularSequentialIsometry


-- Both directions compute to the original injection, through only the
-- constructor computation rules of the intermediate maps.

toRegular-ι : ∀ x → toRegular (S.ι x) ≡ Regular.ι x
toRegular-ι x =
  cong A.←̂
    (cong R.toExplicitScale (T.toTruncatedScale-ι x)
      ∙ R.toExplicitScale-ι x)

fromRegular-ι : ∀ x → fromRegular (Regular.ι x) ≡ S.ι x
fromRegular-ι x =
  cong F.fromTruncatedScale (R.→ᵣ-ι x)
  ∙ F.fromTruncatedScale-ι x

ι-reflects∼ : ∀ x y ε →
  S.ι x S.∼̂ₛ[ ε ] S.ι y → x PM.≈[ ε ] y
ι-reflects∼ x y ε p =
  C.ι-ι→≈ x y ε (toRegular∼ _ _ ε p)
