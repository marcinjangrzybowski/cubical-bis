open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Equivalence
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

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Refined
  as RefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.ToRefined
  as ToRefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.FromRefined
  as FromRefinedDefinition

module S = SequentialDefinition M'
module A = AlternativeDefinition M'
module R = RefinedDefinition M'
module T = ToRefinedDefinition M'
module F = FromRefinedDefinition M'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


private
  refinedSampleLimit :
    ∀ (x : ℚ₊ → R.ℭ̂ᵣ) g
      (xc : ∀ ε δ →
        x ε R.∼̂ᵣ[ g .Γ.γ ε +₊ g .Γ.γ δ ] x δ)
      (z : ℚ₊ → R.ℭ̂ᵣ)
      (zc : ∀ ε δ → z ε R.∼̂ᵣ[ ε +₊ δ ] z δ)
      (pointwise : ∀ ε →
        z ε ≡ x (g .Γ.τ
          (F.dyadicRadius (F.samplingModulus ε))))
    → R.lim z ∣ Γid , zc ∣₁ ≡ R.lim x ∣ g , xc ∣₁
  refinedSampleLimit x g xc z zc pointwise = R.eqℭ _ _ close
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


toRefined-fromRefined : ∀ x → T.toRefined (F.fromRefined x) ≡ x
toRefined-fromRefined = R.Elimℭ̂ᵣ-Prop.go e
  where
  e : R.Elimℭ̂ᵣ-Prop (λ x → T.toRefined (F.fromRefined x) ≡ x)
  e .R.Elimℭ̂ᵣ-Prop.ιA x =
    cong T.toRefined (F.fromRefined-ι x) ∙ T.toRefined-ι x
  e .R.Elimℭ̂ᵣ-Prop.limA x gx IH =
    PT.elim
      (λ gx → R.isSetℭ̂ᵣ
        (T.toRefined (F.fromRefined (R.lim x gx))) (R.lim x gx))
      (λ { (g , xc) →
        let sc = F.sampleFamilyCauchy (F.fromRefined ∘ x) g
              (λ ε δ → F.fromRefinedSlack (x ε) (x δ)
                (g .Γ.γ ε +₊ g .Γ.γ δ) (xc ε δ))
            z = λ ε → T.toRefined
              (F.sampleFamily (F.fromRefined ∘ x) g
                (F.samplingModulus ε))
        in
          cong T.toRefined (F.fromRefined-lim-canonical x g xc)
        ∙ T.toRefined-lim-canonical
            (F.sampleFamily (F.fromRefined ∘ x) g)
            F.samplingModulus (sc .snd)
        ∙ refinedSampleLimit x g xc z _
            (λ ε → IH (g .Γ.τ
              (F.dyadicRadius (F.samplingModulus ε)))) }) gx
  e .R.Elimℭ̂ᵣ-Prop.isPropA x = R.isSetℭ̂ᵣ _ _


fromRefined-toRefined : ∀ x → F.fromRefined (T.toRefined x) ≡ x
fromRefined-toRefined = S.Elimℭ̂ₛ-Prop.go e
  where
  e : S.Elimℭ̂ₛ-Prop (λ x → F.fromRefined (T.toRefined x) ≡ x)
  e .S.Elimℭ̂ₛ-Prop.ιA x =
    cong F.fromRefined (T.toRefined-ι x) ∙ F.fromRefined-ι x
  e .S.Elimℭ̂ₛ-Prop.limA x gx IH =
    PT.elim
      (λ gx → S.isSetℭ̂ₛ
        (F.fromRefined (T.toRefined (S.lim x gx))) (S.lim x gx))
      (λ { (μ , xc) →
        let y = λ ε → T.toRefined (x (μ ε))
            rc = T.regularizedFamilyCauchy (T.toRefined ∘ x) μ
              (λ ε m n με≤m με≤n →
                T.toRefined∼ (x m) (x n) ε
                  (xc ε m n με≤m με≤n))
            z = F.sampleFamily (F.fromRefined ∘ y) Γid
        in
          cong F.fromRefined (T.toRefined-lim-canonical x μ xc)
        ∙ F.fromRefined-lim-canonical y Γid rc
        ∙ sequentialSampleLimit x μ xc z _
            (λ n → IH (μ (F.dyadicRadius n))) }) gx
  e .S.Elimℭ̂ₛ-Prop.isPropA x = S.isSetℭ̂ₛ _ _


moreRefinedIso : Iso S.ℭ̂ₛ R.ℭ̂ᵣ
moreRefinedIso .Iso.fun = T.toRefined
moreRefinedIso .Iso.inv = F.fromRefined
moreRefinedIso .Iso.sec = toRefined-fromRefined
moreRefinedIso .Iso.ret = fromRefined-toRefined

moreRefinedEquiv : S.ℭ̂ₛ ≃ R.ℭ̂ᵣ
moreRefinedEquiv = isoToEquiv moreRefinedIso


alternativeMoreRefinedIso : Iso S.ℭ̂ₛ A.ℭ̂
alternativeMoreRefinedIso .Iso.fun = R.fromRefined ∘ T.toRefined
alternativeMoreRefinedIso .Iso.inv = F.fromRefined ∘ R.→ᵣ
alternativeMoreRefinedIso .Iso.sec x =
    cong R.fromRefined (toRefined-fromRefined (R.→ᵣ x))
  ∙ R.fromRefined→ᵣ x
alternativeMoreRefinedIso .Iso.ret x =
    cong F.fromRefined (R.→ᵣfromRefined (T.toRefined x))
  ∙ fromRefined-toRefined x

alternativeMoreRefinedEquiv : S.ℭ̂ₛ ≃ A.ℭ̂
alternativeMoreRefinedEquiv = isoToEquiv alternativeMoreRefinedIso
