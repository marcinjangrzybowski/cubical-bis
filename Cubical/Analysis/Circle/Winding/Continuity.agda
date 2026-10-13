module Cubical.Analysis.Circle.Winding.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Circle.Metric
open import Cubical.Analysis.Circle.Winding.Subdivision

-- Only the modulus at a single fixed radius is used.  Its witness remains
-- truncated; no sequence of choices is needed to obtain a fine subdivision.
fine-uniform : (f : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
  ∥ Σ[ n ∈ ℕ ] Subdivision.Fine (fst f ∘ rat) n 0 1 ∥₁
fine-uniform f = PT.map
  (λ (μ , continuous) → Subdivision.fine-exists (fst f ∘ rat) (μ quarter)
    (λ x y close → IsUniformlyContinuousWith.pres≈ continuous
      (rat x) (rat y) quarter (rat-rat x y (μ quarter) close)))
  (snd f)
