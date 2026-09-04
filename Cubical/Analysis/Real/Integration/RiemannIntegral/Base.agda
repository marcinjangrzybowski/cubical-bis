module Cubical.Analysis.Real.Integration.RiemannIntegral.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ using (_/2₊)
open 1/2∈ℚ using (/2+/2≡id)

open import Cubical.Relation.Premetric.Base using (PremetricStr)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra


private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)


HasRiemannIntegralOn : (ℝ → ℝ) → ℝ → ℝ → ℝ → Type₀
HasRiemannIntegralOn f a b value =
  ∀ (ε : ℚ₊) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ (tagged : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition.partition tagged) δ →
        absℝ (riemannSum tagged f - value) <ℝ rat (fst ε))


isPropHasRiemannIntegralOn : ∀ f a b value →
  isProp (HasRiemannIntegralOn f a b value)
isPropHasRiemannIntegralOn f a b value hasValue hasValue' =
  funExt λ ε → squash₁ (hasValue ε) (hasValue' ε)


IsRiemannIntegrableOn : (ℝ → ℝ) → ℝ → ℝ → Type₀
IsRiemannIntegrableOn f a b =
  Σ[ value ∈ ℝ ] HasRiemannIntegralOn f a b value


integral : ∀ {f a b} → IsRiemannIntegrableOn f a b → ℝ
integral = fst


fineTaggedPartition : ∀ a b → a ≤ℝ b →
  ∀ δ →
  ∃[ tagged ∈ TaggedPartition[ a , b ] ]
    HasMeshBelow (TaggedPartition.partition tagged) δ
fineTaggedPartition a b a≤b δ =
  PT.map
    (λ { (N , fineTail) →
      dyadicLeftTaggedPartition a b a≤b N
      , fineTail N ℕ.≤-refl })
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b δ)


riemannIntegralUnique : ∀ a b → a ≤ℝ b → ∀ f value value' →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn f a b value' →
  value ≡ value'
riemannIntegralUnique a b a≤b f value value' hasValue hasValue' =
  eqℝ value value' λ ε →
    PT.rec2 (Pℝ.isProp≈ value value' ε)
      (λ { (δ , closeToValue) (δ' , closeToValue') →
        PT.rec (Pℝ.isProp≈ value value' ε)
          (λ { (tagged , fine) →
            Pℝ.subst≈ value value' (/2+/2≡id (fst ε))
              (triangle∼ value (riemannSum tagged f) value'
                (ε /2₊) (ε /2₊)
                (sym∼ (riemannSum tagged f) value (ε /2₊)
                  (absDifference<→closeness
                    (riemannSum tagged f) value (ε /2₊)
                    (closeToValue tagged
                      (meshBelowMonotone
                        (TaggedPartition.partition tagged)
                        (min₊ δ δ') δ (min₊≤L δ δ') fine))))
                (absDifference<→closeness
                  (riemannSum tagged f) value' (ε /2₊)
                  (closeToValue' tagged
                    (meshBelowMonotone
                      (TaggedPartition.partition tagged)
                      (min₊ δ δ') δ' (min₊≤R δ δ') fine)))) })
          (fineTaggedPartition a b a≤b (min₊ δ δ')) })
      (hasValue (ε /2₊))
      (hasValue' (ε /2₊))


isPropIsRiemannIntegrableOn : ∀ a b → a ≤ℝ b → ∀ f →
  isProp (IsRiemannIntegrableOn f a b)
isPropIsRiemannIntegrableOn a b a≤b f
  (value , hasValue) (value' , hasValue') =
  Σ≡Prop
    (λ candidate → isPropHasRiemannIntegralOn f a b candidate)
    (riemannIntegralUnique
      a b a≤b f value value' hasValue hasValue')
