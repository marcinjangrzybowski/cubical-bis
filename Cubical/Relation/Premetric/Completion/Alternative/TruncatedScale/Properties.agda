open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale.Properties
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Properties
  as AlternativePropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition

module A = AlternativeDefinition M'
module AP = AlternativePropertiesDefinition M'
module R = TruncatedScaleDefinition M'

open PositiveRationals


-- The inverse of the isomorphism also reflects closeness.  Consequently all
-- premetric laws can be transferred without repeating their radius proofs.

toExplicitScale-reflects∼ : ∀ x y ε →
  R.toExplicitScale x A.∼̂[ ε ] R.toExplicitScale y →
  x R.∼̂ᵣ[ ε ] y
toExplicitScale-reflects∼ x y ε p =
  subst2 (λ u v → u R.∼̂ᵣ[ ε ] v)
    (R.→ᵣtoExplicitScale x) (R.→ᵣtoExplicitScale y)
    (R.∼→ᵣ _ _ _ p)

toExplicitScale-closenessEquiv : ∀ x y ε →
  (x R.∼̂ᵣ[ ε ] y) ≃
  (R.toExplicitScale x A.∼̂[ ε ] R.toExplicitScale y)
toExplicitScale-closenessEquiv x y ε = propBiimpl→Equiv
  (R.isProp∼ x ε y)
  (A.isProp∼ (R.toExplicitScale x) ε (R.toExplicitScale y))
  (R.toExplicitScale∼ x y ε)
  (toExplicitScale-reflects∼ x y ε)


isSym∼̂ᵣ : ∀ x y ε → x R.∼̂ᵣ[ ε ] y → y R.∼̂ᵣ[ ε ] x
isSym∼̂ᵣ x y ε p = toExplicitScale-reflects∼ y x ε
  (AP.isSym∼̂ _ _ ε (R.toExplicitScale∼ x y ε p))

isTriangular∼̂ᵣ : ∀ x y z ε δ →
  x R.∼̂ᵣ[ ε ] y → y R.∼̂ᵣ[ δ ] z →
  x R.∼̂ᵣ[ ε +₊ δ ] z
isTriangular∼̂ᵣ x y z ε δ p q =
  toExplicitScale-reflects∼ x z (ε +₊ δ)
    (AP.isTriangular∼̂ _ _ _ ε δ
      (R.toExplicitScale∼ x y ε p) (R.toExplicitScale∼ y z δ q))

isRounded∼̂ᵣ : ∀ x y ε →
  x R.∼̂ᵣ[ ε ] y →
  ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x R.∼̂ᵣ[ δ ] y)
isRounded∼̂ᵣ x y ε p = PT.map
  (λ (δ , δ<ε , q) →
    δ , δ<ε , toExplicitScale-reflects∼ x y δ q)
  (AP.isRounded∼̂ _ _ ε (R.toExplicitScale∼ x y ε p))


ℭ̂ᵣIsPremetric : IsPremetric R._∼̂ᵣ[_]_
IsPremetric.isSetM ℭ̂ᵣIsPremetric = R.isSetℭ̂ᵣ
IsPremetric.isProp≈ ℭ̂ᵣIsPremetric x y ε = R.isProp∼ x ε y
IsPremetric.isRefl≈ ℭ̂ᵣIsPremetric = R.isRefl∼̂ᵣ
IsPremetric.isSym≈ ℭ̂ᵣIsPremetric = isSym∼̂ᵣ
IsPremetric.isSeparated≈ ℭ̂ᵣIsPremetric = R.eqℭ
IsPremetric.isTriangular≈ ℭ̂ᵣIsPremetric = isTriangular∼̂ᵣ
IsPremetric.isRounded≈ ℭ̂ᵣIsPremetric = isRounded∼̂ᵣ

ℭ̂ᵣPremetricSpace :
  PremetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
ℭ̂ᵣPremetricSpace .fst = R.ℭ̂ᵣ
PremetricStr._≈[_]_ (ℭ̂ᵣPremetricSpace .snd) = R._∼̂ᵣ[_]_
PremetricStr.isPremetric (ℭ̂ᵣPremetricSpace .snd) = ℭ̂ᵣIsPremetric


-- These two constructor equalities are immediate in the truncated-scale
-- presentation.  In particular, changing the scale requires no metric
-- argument analogous to Alternative.g-irrelevant.

limWitnessIrrelevant : ∀ x gx gy → R.lim x gx ≡ R.lim x gy
limWitnessIrrelevant x gx gy = cong (R.lim x) (squash₁ gx gy)

limCong : ∀ x y gx gy → x ≡ y → R.lim x gx ≡ R.lim y gy
limCong x y gx gy p = cong (λ z → R.lim (fst z) (snd z)) pairPath
  where
  pairPath : (x , gx) ≡ (y , gy)
  pairPath = Σ≡Prop (λ _ → squash₁) p
