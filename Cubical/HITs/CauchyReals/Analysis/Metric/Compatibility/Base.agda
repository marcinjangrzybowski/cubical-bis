module Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base using
  (IsUContinuous)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric


IsUContinuous→IsUniformlyContinuousWith :
  ∀ f → (f-uc : IsUContinuous f) →
  IsUniformlyContinuousWith
    (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
    (λ ε → fst (f-uc ε))
IsUniformlyContinuousWith.pres≈
  (IsUContinuous→IsUniformlyContinuousWith f f-uc) x y ε x≈y =
  ∼→≈ℝ (f x) (f y) ε
    (snd (f-uc ε) x y
      (≈ℝ→∼ x y (fst (f-uc ε)) x≈y))


IsUContinuous→ℝUC : ∀ f → IsUContinuous f →
  UC[ ℝPremetricSpace , ℝPremetricSpace ]
fst (IsUContinuous→ℝUC f f-uc) = f
snd (IsUContinuous→ℝUC f f-uc) =
  ∣ (λ ε → fst (f-uc ε)) ,
    IsUContinuous→IsUniformlyContinuousWith f f-uc ∣₁


IsUniformlyContinuousWith→IsUContinuous :
  ∀ f mu →
  IsUniformlyContinuousWith
    (snd ℝPremetricSpace) f (snd ℝPremetricSpace) mu →
  IsUContinuous f
IsUniformlyContinuousWith→IsUContinuous f mu mu-uc ε =
  mu ε , λ x y x∼y →
    ≈ℝ→∼ (f x) (f y) ε
      (IsUniformlyContinuousWith.pres≈ mu-uc x y ε
        (∼→≈ℝ x y (mu ε) x∼y))


ℝUC→∥IsUContinuous∥ :
  (f : UC[ ℝPremetricSpace , ℝPremetricSpace ]) →
  ∥ IsUContinuous (fst f) ∥₁
ℝUC→∥IsUContinuous∥ f = PT.map
  (λ (mu , mu-uc) →
    IsUniformlyContinuousWith→IsUContinuous
      (fst f) mu mu-uc)
  (snd f)
