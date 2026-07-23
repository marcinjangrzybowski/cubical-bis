module Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Predicate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace
  using (PremetricSubspace)

open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base
  using (IsUContinuousℙ)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric


IsUContinuousℙ→IsUniformlyContinuousWith :
  (P : ℙ ℝ) (f : ∀ x → x ∈ P → ℝ) →
  (f-uc : IsUContinuousℙ P f) →
  IsUniformlyContinuousWith
    (snd (PremetricSubspace ℝPremetricSpace P))
    (λ x → f (fst x) (snd x))
    (snd ℝPremetricSpace)
    (λ ε → fst (f-uc ε))
IsUniformlyContinuousWith.pres≈
  (IsUContinuousℙ→IsUniformlyContinuousWith P f f-uc)
  (x , x∈) (y , y∈) ε x≈y =
  ∼→≈ℝ (f x x∈) (f y y∈) ε
    (snd (f-uc ε) x y x∈ y∈
      (≈ℝ→∼ x y (fst (f-uc ε)) x≈y))


IsUContinuousℙ→ℝSubspaceUC :
  (P : ℙ ℝ) (f : ∀ x → x ∈ P → ℝ) →
  IsUContinuousℙ P f →
  UC[ PremetricSubspace ℝPremetricSpace P , ℝPremetricSpace ]
fst (IsUContinuousℙ→ℝSubspaceUC P f f-uc) (x , x∈) = f x x∈
snd (IsUContinuousℙ→ℝSubspaceUC P f f-uc) =
  ∣ (λ ε → fst (f-uc ε)) ,
    IsUContinuousℙ→IsUniformlyContinuousWith P f f-uc ∣₁


IsUniformlyContinuousWith→IsUContinuousℙ :
  (P : ℙ ℝ) (f : ∀ x → x ∈ P → ℝ) (mu : ℚ₊ → ℚ₊) →
  IsUniformlyContinuousWith
    (snd (PremetricSubspace ℝPremetricSpace P))
    (λ x → f (fst x) (snd x))
    (snd ℝPremetricSpace)
    mu →
  IsUContinuousℙ P f
IsUniformlyContinuousWith→IsUContinuousℙ P f mu mu-uc ε =
  mu ε , λ x y x∈ y∈ x∼y →
    ≈ℝ→∼ (f x x∈) (f y y∈) ε
      (IsUniformlyContinuousWith.pres≈ mu-uc
        (x , x∈) (y , y∈) ε
        (∼→≈ℝ x y (mu ε) x∼y))


ℝSubspaceUC→∥IsUContinuousℙ∥ :
  (P : ℙ ℝ)
  (f : UC[ PremetricSubspace ℝPremetricSpace P , ℝPremetricSpace ]) →
  ∥ IsUContinuousℙ P (λ x x∈ → fst f (x , x∈)) ∥₁
ℝSubspaceUC→∥IsUContinuousℙ∥ P f = PT.map
  (λ (mu , mu-uc) →
    IsUniformlyContinuousWith→IsUContinuousℙ
      P (λ x x∈ → fst f (x , x∈)) mu mu-uc)
  (snd f)
