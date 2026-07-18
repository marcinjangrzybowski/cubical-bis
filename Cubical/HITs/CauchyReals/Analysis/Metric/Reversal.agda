module Cubical.HITs.CauchyReals.Analysis.Metric.Reversal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Foundations.Powerset

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Unit using (tt)

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base using
  (IsUContinuous)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


private
  zeroℝ oneℝ : ℝ
  zeroℝ = ℕ.HasFromNat.fromNat fromNatℝ ℕ.zero {{tt}}
  oneℝ = ℕ.HasFromNat.fromNat fromNatℝ (ℕ.suc ℕ.zero) {{tt}}


reversalPreserves∼ : ∀ u v ε →
  u ∼[ ε ] v → (oneℝ -ᵣ u) ∼[ ε ] (oneℝ -ᵣ v)
reversalPreserves∼ u v ε u∼v =
  invEq (∼≃abs<ε _ _ _)
    (isTrans≡<ᵣ _ _ _
      (cong absᵣ ℝ! ∙ sym (minusComm-absᵣ u v))
      (fst (∼≃abs<ε _ _ _) u∼v))


reversalIsUContinuous : IsUContinuous (λ x → oneℝ -ᵣ x)
reversalIsUContinuous ε = ε , λ u v → reversalPreserves∼ u v ε


reversalIsNonExpanding :
  IsNonExpanding
    (snd ℝPremetricSpace) (λ x → oneℝ -ᵣ x) (snd ℝPremetricSpace)
IsNonExpanding.pres≈ reversalIsNonExpanding u v ε u≈v =
  ∼→≈ℝ (oneℝ -ᵣ u) (oneℝ -ᵣ v) ε
    (reversalPreserves∼ u v ε (≈ℝ→∼ u v ε u≈v))


reversalℝNE : NE[ ℝPremetricSpace , ℝPremetricSpace ]
reversalℝNE = (λ x → oneℝ -ᵣ x) , reversalIsNonExpanding


reversalℝUC : UC[ ℝPremetricSpace , ℝPremetricSpace ]
reversalℝUC = NE→UC reversalℝNE


reversalPreservesUnitInterval : ∀ x →
  x ∈ intervalℙ zeroℝ oneℝ →
  (oneℝ -ᵣ x) ∈ intervalℙ zeroℝ oneℝ
reversalPreservesUnitInterval x (0≤x , x≤1) =
  isTrans≡≤ᵣ _ _ _
    (sym (+-ᵣ oneℝ) ∙ x-ᵣy≡x+ᵣ[-ᵣy] _ _)
    (≤ᵣ-o+ _ _ oneℝ (-ᵣ≤ᵣ _ _ x≤1))
  , isTrans≤≡ᵣ _ _ _
      (≤ᵣ-o+ _ _ oneℝ (-ᵣ≤ᵣ _ _ 0≤x))
      (sym (x-ᵣy≡x+ᵣ[-ᵣy] _ _) ∙ -ᵣ-rat₂ _ _)


unitIntervalReversalUC :
  UC[ UnitIntervalPremetricSpace , UnitIntervalPremetricSpace ]
unitIntervalReversalUC =
  restrictUC (intervalℙ zeroℝ oneℝ) (intervalℙ zeroℝ oneℝ)
    reversalℝUC reversalPreservesUnitInterval
