module Cubical.Relation.Premetric.Completion.Alternative.Refined.LiftRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.LiftRationals
  as Existing
import Cubical.Relation.Premetric.Completion.Alternative.Refined
  as RefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Refined.Properties
  as RefinedPropertiesDefinition

module R = RefinedDefinition ℚPremetricSpace
module RP = RefinedPropertiesDefinition ℚPremetricSpace

open PositiveRationals


-- Unlike the untruncated alternative constructor, the refined limit can use
-- a merely existing local Lipschitz constant without selecting one first.

IsMerelyLocallyLipschitz : (ℚ → ℚ) → Type₀
IsMerelyLocallyLipschitz f = ∀ B →
  ∃[ L ∈ ℚ₊ ] Existing.IsLipschitzOnBallWith f B L

isPropIsMerelyLocallyLipschitz : ∀ f →
  isProp (IsMerelyLocallyLipschitz f)
isPropIsMerelyLocallyLipschitz f = isPropΠ λ _ → squash₁

locallyLipschitz→merely : ∀ {f} →
  Existing.IsLocallyLipschitz f → IsMerelyLocallyLipschitz f
locallyLipschitz→merely f-local B = ∣ f-local B ∣₁

boundedImageWitness : ∀ f B
  → (x : ℚ₊ → ℚ)
  → Existing.IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ∃[ L ∈ ℚ₊ ] Existing.IsLipschitzOnBallWith f B L
  → R.ScaleWitness (R.ι ∘ f ∘ x)
boundedImageWitness f B x x-bounded xc = PT.map build
  where
  build : Σ[ L ∈ ℚ₊ ] Existing.IsLipschitzOnBallWith f B L →
    Σ[ g ∈ Γ ]
      (∀ ε δ →
        R.ι (f (x ε)) R.∼̂ᵣ[
          g .Γ.γ ε +₊ g .Γ.γ δ
        ] R.ι (f (x δ)))
  build (L , f-local) = Existing.imageScaleΓ L , λ ε δ →
    R.ι-ι (f (x ε)) (f (x δ)) _
      (Existing.boundedCauchyImageScaled
        f B L f-local x x-bounded xc ε δ)

boundedCauchyLimitMere : ∀ f B
  → (x : ℚ₊ → ℚ)
  → Existing.IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ∃[ L ∈ ℚ₊ ] Existing.IsLipschitzOnBallWith f B L
  → R.ℭ̂ᵣ
boundedCauchyLimitMere f B x x-bounded xc f-local =
  R.lim (R.ι ∘ f ∘ x)
    (boundedImageWitness f B x x-bounded xc f-local)

boundedCauchyLimitWith : ∀ f B L
  → Existing.IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → Existing.IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → R.ℭ̂ᵣ
boundedCauchyLimitWith f B L f-local x x-bounded xc =
  boundedCauchyLimitMere f B x x-bounded xc ∣ L , f-local ∣₁

boundedCauchyLimitMere-β : ∀ f B L f-local x x-bounded xc →
  boundedCauchyLimitMere f B x x-bounded xc ∣ L , f-local ∣₁ ≡
    boundedCauchyLimitWith f B L f-local x x-bounded xc
boundedCauchyLimitMere-β f B L f-local x x-bounded xc = refl

boundedCauchyLimitMere-independent :
  ∀ f B x x-bounded xc fL fK →
  boundedCauchyLimitMere f B x x-bounded xc fL ≡
    boundedCauchyLimitMere f B x x-bounded xc fK
boundedCauchyLimitMere-independent f B x x-bounded xc fL fK =
  RP.limWitnessIrrelevant (R.ι ∘ f ∘ x) _ _

boundedCauchyLimitWith-independent :
  ∀ f B L K fL fK x x-bounded xc →
  boundedCauchyLimitWith f B L fL x x-bounded xc ≡
    boundedCauchyLimitWith f B K fK x x-bounded xc
boundedCauchyLimitWith-independent f B L K fL fK x x-bounded xc =
  RP.limWitnessIrrelevant (R.ι ∘ f ∘ x) _ _

boundedCauchyLimitWith-fromAlternative :
  ∀ f B L f-local x x-bounded xc →
  R.→ᵣ
      (Existing.boundedCauchyLimitDirect
        f B L f-local x x-bounded xc)
    ≡ boundedCauchyLimitWith f B L f-local x x-bounded xc
boundedCauchyLimitWith-fromAlternative
  f B L f-local x x-bounded xc = refl


-- Clamping gives a bounded representative of any rational Cauchy family, so
-- mere local Lipschitzness is sufficient to construct its image limit.

locallyLipschitzCauchyLimitMere : ∀ f
  → IsMerelyLocallyLipschitz f
  → (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → R.ℭ̂ᵣ
locallyLipschitzCauchyLimitMere f f-local x xc =
  boundedCauchyLimitMere f B tail tail-bounded tail-cauchy (f-local B)
  where
  tail : ℚ₊ → ℚ
  tail = Existing.cauchyTail x

  B : ℚ₊
  B = Existing.cauchyTailBound x

  tail-bounded : Existing.IsBoundedBy B tail
  tail-bounded = Existing.cauchyTailBounded x xc

  tail-cauchy : PremetricTheory.isCauchy ℚPremetricSpace tail
  tail-cauchy = Existing.cauchyTailCauchy x xc

signedSquareℚ-merelyLocallyLipschitz :
  IsMerelyLocallyLipschitz signedSquareℚ
signedSquareℚ-merelyLocallyLipschitz B =
  ∣ Existing.signedSquareℚ-locallyLipschitz B ∣₁

signedSquareCauchyLimitMere : (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → R.ℭ̂ᵣ
signedSquareCauchyLimitMere =
  locallyLipschitzCauchyLimitMere signedSquareℚ
    signedSquareℚ-merelyLocallyLipschitz


-- This construction interprets the image of each rational Cauchy family.
-- It is not by itself a map ℭ̂ᵣ → ℭ̂ᵣ for an arbitrary locally
-- Lipschitz function: such a map must additionally respect the relations
-- between all nested limits.  Globally Lipschitz maps are handled by
-- Refined.Functor; signed squaring deliberately lies outside that case.
