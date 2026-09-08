module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareDegeneracies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (squash₁)
open import Cubical.Functions.Embedding using (isEmbedding; injEmbedding)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.Pushout.Properties as PO
open import Cubical.HITs.Pushout.KrausVonRaumer using (preserveHLevelEmbedding)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (Interval; IntervalSquare; 𝟘)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real using (constantUC)
open CategoryStructures using (_∘UC_; UC≡)

module SquareDegeneracies {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  private
    module PX = PremetricStr (snd X)

  EdgeCube : Type (ℓ-max ℓ ℓ')
  EdgeCube = UC[ Interval , X ]

  SquareCube : Type (ℓ-max ℓ ℓ')
  SquareCube = UC[ IntervalSquare , X ]

  isSetEdgeCube : isSet EdgeCube
  isSetEdgeCube = isSetΣSndProp (isSet→ PX.isSetM) (λ _ → squash₁)

  isSetSquareCube : isSet SquareCube
  isSetSquareCube = isSetΣSndProp (isSet→ PX.isSetM) (λ _ → squash₁)

  constant : fst X → EdgeCube
  constant = constantUC

  horizontal vertical : EdgeCube → SquareCube
  horizontal p = p ∘UC productFstUC
  vertical p = p ∘UC productSndUC

  constant-square : (x : fst X) → horizontal (constant x) ≡ vertical (constant x)
  constant-square x = UC≡ refl

  -- Equality of the two degeneracy presentations determines their
  -- common constant value by endpoint evaluation, without any decision.
  intersection : (p q : EdgeCube) → horizontal p ≡ vertical q →
    Σ[ x ∈ fst X ] (constant x ≡ p) × (constant x ≡ q)
  intersection p q same = fst p 𝟘 ,
    UC≡ (funExt (λ t → cong (λ (s : SquareCube) → fst s (𝟘 , 𝟘)) same ∙
      sym (cong (λ (s : SquareCube) → fst s (t , 𝟘)) same))) ,
    UC≡ (funExt (λ t → cong (λ (s : SquareCube) → fst s (𝟘 , t)) same))

  private
    constant-injective : ∀ {x y} → constant x ≡ constant y → x ≡ y
    constant-injective = cong (λ (p : EdgeCube) → fst p 𝟘)

    horizontal-injective : ∀ {p q} → horizontal p ≡ horizontal q → p ≡ q
    horizontal-injective same = UC≡ (funExt (λ t → cong (λ (s : SquareCube) → fst s (t , 𝟘)) same))

    vertical-injective : ∀ {p q} → vertical p ≡ vertical q → p ≡ q
    vertical-injective same = UC≡ (funExt (λ t → cong (λ (s : SquareCube) → fst s (𝟘 , t)) same))

  -- Retain the overlap eliminator. Setness is proved from the embeddings;
  -- it is not imposed by a truncation constructor.
  Latching₂ : Type (ℓ-max ℓ ℓ')
  Latching₂ = Pushout constant constant

  opaque
    isSetLatching₂ : isSet Latching₂
    isSetLatching₂ = preserveHLevelEmbedding constant constant {n = zero}
      (injEmbedding {f = constant} isSetEdgeCube constant-injective)
      (injEmbedding {f = constant} isSetEdgeCube constant-injective)
      isSetEdgeCube isSetEdgeCube

  latchingMap : Latching₂ → SquareCube
  latchingMap (inl p) = horizontal p
  latchingMap (inr q) = vertical q
  latchingMap (push x i) = constant-square x i

  private
    includeH includeV : EdgeCube → Latching₂
    includeH = inl
    includeV = inr

    overlap-path : (x : fst X) → includeH (constant x) ≡ includeV (constant x)
    overlap-path = push

    cross : (p q : EdgeCube) → horizontal p ≡ vertical q →
      includeH p ≡ includeV q
    cross p q same = join (intersection p q same)
      where
      join : (Σ[ x ∈ fst X ] (constant x ≡ p) × (constant x ≡ q)) →
        includeH p ≡ includeV q
      join (x , p₀ , q₀) = cong includeH (sym p₀) ∙∙ overlap-path x ∙∙ cong includeV q₀

    injective : (u v : Latching₂) → latchingMap u ≡ latchingMap v → u ≡ v
    injective = PO.elimProp
      (λ u → (v : Latching₂) → latchingMap u ≡ latchingMap v → u ≡ v)
      (λ u → isPropΠ (λ v → isProp→ (isSetLatching₂ u v)))
      (λ p → PO.elimProp
        (λ v → horizontal p ≡ latchingMap v → includeH p ≡ v)
        (λ v → isProp→ (isSetLatching₂ (includeH p) v))
        (λ q same → cong includeH (horizontal-injective same)) (cross p))
      (λ q → PO.elimProp
        (λ v → vertical q ≡ latchingMap v → includeV q ≡ v)
        (λ v → isProp→ (isSetLatching₂ (includeV q) v))
        (λ p same → sym (cross p q (sym same)))
        (λ p same → cong includeV (vertical-injective same)))

  isEmbeddingLatching₂ : isEmbedding latchingMap
  isEmbeddingLatching₂ = injEmbedding {f = latchingMap} isSetSquareCube
    (λ {u} {v} → injective u v)
