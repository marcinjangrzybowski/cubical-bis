module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PointFreeCover where

-- The inductively generated cover used to STATE the proposed localic FTA.
-- Parameters describe generators and cover rules; no cover law or FTA is
-- assumed. Keeping this definition generic also bounds elaboration costs.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

module GeneratedCover (Basic Scale : Type₀) (whole : Basic)
  (refines inside : Basic → Basic → Type₀)
  (uniformFamily : Scale → Basic → Type₀) (excluded : Basic → Type₀) where

  intersection : (Basic → Type₀) → Basic → Basic → Type₀
  intersection U b c = ∥ Σ[ a ∈ Basic ] (U a × refines c a × refines c b) ∥₁

  data Cover : Basic → (Basic → Type₀) → Type₁ where
    contains : ∀ {a U} → U a → Cover a U
    refine : ∀ {a b U} → refines a b → Cover b U → Cover a U
    compose : ∀ {a U V} → Cover a U → ((b : Basic) → U b → Cover b V) → Cover a V
    localize : ∀ {a b c U} → Cover a U → refines c a → refines c b → Cover c (intersection U b)
    round : (a : Basic) → Cover a (λ b → inside b a)
    uniform : (ε : Scale) → Cover whole (uniformFamily ε)
    exclude : ∀ {a} → excluded a → Cover a (λ _ → ⊥)
    coverIsProp : ∀ {a U} (c d : Cover a U) → c ≡ d
