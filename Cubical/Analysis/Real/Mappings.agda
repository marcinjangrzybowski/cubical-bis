module Cubical.Analysis.Real.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base


constantRealMapIsNonExpanding : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (value : ℝ) →
  IsNonExpanding source (λ _ → value) (ℝPremetricSpace .snd)
constantRealMapIsNonExpanding source value
    .IsNonExpanding.pres≈ _ _ ε _ = refl∼ value ε

constantRealMapIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (value : ℝ) →
  isContinuous source (λ _ → value) (ℝPremetricSpace .snd)
constantRealMapIsContinuous source value =
  isNonExpanding→isContinuous source (λ _ → value) (ℝPremetricSpace .snd)
    (constantRealMapIsNonExpanding source value)

identityRealMapIsContinuous :
  isContinuous (ℝPremetricSpace .snd) (idfun ℝ) (ℝPremetricSpace .snd)
identityRealMapIsContinuous =
  snd (NE→C (CategoryStructures.idⁿ {M = ℝPremetricSpace}))
