open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.Equivalence
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.To
  as ToTruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.From
  as FromTruncatedScaleDefinition

module S = SequentialDefinition M'
module A = AlternativeDefinition M'
module R = TruncatedScaleDefinition M'
module T = ToTruncatedScaleDefinition M'
module F = FromTruncatedScaleDefinition M'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


private
  truncatedScaleSampleLimit :
    ∀ (x : ℚ₊ → R.ℭ̂ᵣ) g
      (xc : ∀ ε δ →
        x ε R.∼̂ᵣ[ g .Γ.γ ε +₊ g .Γ.γ δ ] x δ)
      (z : ℚ₊ → R.ℭ̂ᵣ)
      (zc : ∀ ε δ → z ε R.∼̂ᵣ[ ε +₊ δ ] z δ)
      (pointwise : ∀ ε →
        z ε ≡ x (g .Γ.τ
          (F.dyadicRadius (F.samplingModulus ε))))
    → R.lim z ∣ Γid , zc ∣₁ ≡ R.lim x ∣ g , xc ∣₁
  truncatedScaleSampleLimit x g xc z zc pointwise = R.eqℭ _ _ close
    where
    close : ∀ ε →
      R.lim z ∣ Γid , zc ∣₁ R.∼̂ᵣ[ ε ] R.lim x ∣ g , xc ∣₁
    close ε = R.lim-lim z Γid x g ε θ a zc xc Δ inner
      where
      θ = ε /4₊
      a = g .Γ.τ (F.dyadicRadius (F.samplingModulus θ))

      ga<θ/4 : fst (g .Γ.γ a) <ℚ fst (θ /4₊)
      ga<θ/4 = begin<
        fst (g .Γ.γ a) ≤⟨ g .Γ.γ∘τ≤id _ ⟩
        fst (F.dyadicRadius (F.samplingModulus θ))
          <⟨ F.samplingModulus-small θ ⟩
        fst (θ /4₊) ◾

      ga<θ : fst (g .Γ.γ a) <ℚ fst θ
      ga<θ = ℚ.isTrans< _ _ _ ga<θ/4 (/4₊<id θ)

      outer = θ +₊ g .Γ.γ a

      outer<ε : outer <₊ ε
      outer<ε = begin<
        fst outer <⟨ +MonoL< _ _ (fst θ) ga<θ ⟩
        fst (θ +₊ θ) ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
        fst (ε /2₊) <⟨ /2₊<id ε ⟩
        fst ε ◾

      Δ : 0 ℚ.< ε -₊ outer
      Δ = <→0<Δ (fst outer) (fst ε) outer<ε

      target = (ε -₊ outer , Δ)

      inner : z θ R.∼̂ᵣ[ target ] x a
      inner = subst (λ w → w R.∼̂ᵣ[ target ] x a)
        (sym (pointwise θ)) (R.isRefl∼̂ᵣ (x a) target)


  sequentialSampleLimit :
    ∀ (x : ℕ → S.ℭ̂ₛ) μ
      (xc : ∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
        x m S.∼̂ₛ[ ε ] x n)
      (z : ℕ → S.ℭ̂ₛ)
      (zc : ∀ ε m n → F.samplingModulus ε ℕ.≤ m →
        F.samplingModulus ε ℕ.≤ n → z m S.∼̂ₛ[ ε ] z n)
      (pointwise : ∀ n →
        z n ≡ x (μ (F.dyadicRadius n)))
    → S.lim z ∣ F.samplingModulus , zc ∣₁ ≡
      S.lim x ∣ μ , xc ∣₁
  sequentialSampleLimit x μ xc z zc pointwise = S.eqℭ _ _ close
    where
    close : ∀ ε →
      S.lim z ∣ F.samplingModulus , zc ∣₁ S.∼̂ₛ[ ε ]
        S.lim x ∣ μ , xc ∣₁
    close ε =
      S.lim-lim z F.samplingModulus x μ ε δ η zc xc Δ inner
      where
      δ = ε /4₊
      η = F.dyadicRadius (F.samplingModulus δ)

      η<δ/4 : fst η <ℚ fst (δ /4₊)
      η<δ/4 = F.samplingModulus-small δ

      η<δ : fst η <ℚ fst δ
      η<δ = ℚ.isTrans< _ _ _ η<δ/4 (/4₊<id δ)

      outer = δ +₊ η

      outer<ε : outer <₊ ε
      outer<ε = begin<
        fst outer <⟨ +MonoL< _ _ (fst δ) η<δ ⟩
        fst (δ +₊ δ) ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
        fst (ε /2₊) <⟨ /2₊<id ε ⟩
        fst ε ◾

      Δ : 0 ℚ.< ε -₊ outer
      Δ = <→0<Δ (fst outer) (fst ε) outer<ε

      target = (ε -₊ outer , Δ)

      inner : z (F.samplingModulus δ) S.∼̂ₛ[ target ] x (μ η)
      inner = subst (λ w → w S.∼̂ₛ[ target ] x (μ η))
        (sym (pointwise (F.samplingModulus δ)))
        (S.isRefl∼̂ₛ (x (μ η)) target)


toTruncatedScale-fromTruncatedScale : ∀ x → T.toTruncatedScale (F.fromTruncatedScale x) ≡ x
toTruncatedScale-fromTruncatedScale = R.Elimℭ̂ᵣ-Prop.go e
  where
  e : R.Elimℭ̂ᵣ-Prop (λ x → T.toTruncatedScale (F.fromTruncatedScale x) ≡ x)
  e .R.Elimℭ̂ᵣ-Prop.ιA x =
    cong T.toTruncatedScale (F.fromTruncatedScale-ι x) ∙ T.toTruncatedScale-ι x
  e .R.Elimℭ̂ᵣ-Prop.limA x gx IH =
    PT.elim
      (λ gx → R.isSetℭ̂ᵣ
        (T.toTruncatedScale (F.fromTruncatedScale (R.lim x gx))) (R.lim x gx))
      (λ { (g , xc) →
        let sc = F.sampleFamilyCauchy (F.fromTruncatedScale ∘ x) g
              (λ ε δ → F.fromTruncatedScaleSlack (x ε) (x δ)
                (g .Γ.γ ε +₊ g .Γ.γ δ) (xc ε δ))
            z = λ ε → T.toTruncatedScale
              (F.sampleFamily (F.fromTruncatedScale ∘ x) g
                (F.samplingModulus ε))
        in
          cong T.toTruncatedScale (F.fromTruncatedScale-lim-canonical x g xc)
        ∙ T.toTruncatedScale-lim-canonical
            (F.sampleFamily (F.fromTruncatedScale ∘ x) g)
            F.samplingModulus (sc .snd)
        ∙ truncatedScaleSampleLimit x g xc z _
            (λ ε → IH (g .Γ.τ
              (F.dyadicRadius (F.samplingModulus ε)))) }) gx
  e .R.Elimℭ̂ᵣ-Prop.isPropA x = R.isSetℭ̂ᵣ _ _


fromTruncatedScale-toTruncatedScale : ∀ x → F.fromTruncatedScale (T.toTruncatedScale x) ≡ x
fromTruncatedScale-toTruncatedScale = S.Elimℭ̂ₛ-Prop.go e
  where
  e : S.Elimℭ̂ₛ-Prop (λ x → F.fromTruncatedScale (T.toTruncatedScale x) ≡ x)
  e .S.Elimℭ̂ₛ-Prop.ιA x =
    cong F.fromTruncatedScale (T.toTruncatedScale-ι x) ∙ F.fromTruncatedScale-ι x
  e .S.Elimℭ̂ₛ-Prop.limA x gx IH =
    PT.elim
      (λ gx → S.isSetℭ̂ₛ
        (F.fromTruncatedScale (T.toTruncatedScale (S.lim x gx))) (S.lim x gx))
      (λ { (μ , xc) →
        let y = λ ε → T.toTruncatedScale (x (μ ε))
            rc = T.regularizedFamilyCauchy (T.toTruncatedScale ∘ x) μ
              (λ ε m n με≤m με≤n →
                T.toTruncatedScale∼ (x m) (x n) ε
                  (xc ε m n με≤m με≤n))
            z = F.sampleFamily (F.fromTruncatedScale ∘ y) Γid
        in
          cong F.fromTruncatedScale (T.toTruncatedScale-lim-canonical x μ xc)
        ∙ F.fromTruncatedScale-lim-canonical y Γid rc
        ∙ sequentialSampleLimit x μ xc z _
            (λ n → IH (μ (F.dyadicRadius n))) }) gx
  e .S.Elimℭ̂ₛ-Prop.isPropA x = S.isSetℭ̂ₛ _ _


sequentialTruncatedScaleIso : Iso S.ℭ̂ₛ R.ℭ̂ᵣ
sequentialTruncatedScaleIso .Iso.fun = T.toTruncatedScale
sequentialTruncatedScaleIso .Iso.inv = F.fromTruncatedScale
sequentialTruncatedScaleIso .Iso.sec = toTruncatedScale-fromTruncatedScale
sequentialTruncatedScaleIso .Iso.ret = fromTruncatedScale-toTruncatedScale

sequentialTruncatedScaleEquiv : S.ℭ̂ₛ ≃ R.ℭ̂ᵣ
sequentialTruncatedScaleEquiv = isoToEquiv sequentialTruncatedScaleIso


sequentialExplicitScaleIso : Iso S.ℭ̂ₛ A.ℭ̂
sequentialExplicitScaleIso .Iso.fun = R.toExplicitScale ∘ T.toTruncatedScale
sequentialExplicitScaleIso .Iso.inv = F.fromTruncatedScale ∘ R.→ᵣ
sequentialExplicitScaleIso .Iso.sec x =
    cong R.toExplicitScale (toTruncatedScale-fromTruncatedScale (R.→ᵣ x))
  ∙ R.toExplicitScale→ᵣ x
sequentialExplicitScaleIso .Iso.ret x =
    cong F.fromTruncatedScale (R.→ᵣtoExplicitScale (T.toTruncatedScale x))
  ∙ fromTruncatedScale-toTruncatedScale x

sequentialExplicitScaleEquiv : S.ℭ̂ₛ ≃ A.ℭ̂
sequentialExplicitScaleEquiv = isoToEquiv sequentialExplicitScaleIso
