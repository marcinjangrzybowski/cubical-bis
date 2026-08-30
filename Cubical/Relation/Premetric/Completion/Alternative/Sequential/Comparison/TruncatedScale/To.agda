open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.To
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale.Properties
  as TruncatedScalePropertiesDefinition

module S = SequentialDefinition M'
module R = TruncatedScaleDefinition M'
module RP = TruncatedScalePropertiesDefinition M'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


private
  TargetCauchySeq : (ℕ → R.ℭ̂ᵣ) → Type _
  TargetCauchySeq x =
    Σ[ μ ∈ (ℚ₊ → ℕ) ]
      (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
        x m R.∼̂ᵣ[ ε ] x n)

  Regularized : (ℕ → R.ℭ̂ᵣ) → (ℚ₊ → ℕ) → ℚ₊ → R.ℭ̂ᵣ
  Regularized x μ ε = x (μ ε)

  regularizedCauchy : ∀ (x : ℕ → R.ℭ̂ᵣ) μ
    → (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
        x m R.∼̂ᵣ[ ε ] x n)
    → ∀ ε δ →
      Regularized x μ ε R.∼̂ᵣ[ ε +₊ δ ] Regularized x μ δ
  regularizedCauchy x μ xc ε δ =
    RP.isTriangular∼̂ᵣ
      (x (μ ε)) (x (ℕ.max (μ ε) (μ δ))) (x (μ δ))
      ε δ
      (xc ε (μ ε) (ℕ.max (μ ε) (μ δ))
        ℕ.≤-refl (ℕ.left-≤-max {m = μ ε} {n = μ δ}))
      (xc δ (ℕ.max (μ ε) (μ δ)) (μ δ)
        (ℕ.right-≤-max {n = μ δ} {m = μ ε}) ℕ.≤-refl)

  regularizedWitness : ∀ (x : ℕ → R.ℭ̂ᵣ) μ
    → (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
        x m R.∼̂ᵣ[ ε ] x n)
    → R.ScaleWitness (Regularized x μ)
  regularizedWitness x μ xc =
    ∣ Γid , regularizedCauchy x μ xc ∣₁

  seqLimitWith : (x : ℕ → R.ℭ̂ᵣ) → TargetCauchySeq x → R.ℭ̂ᵣ
  seqLimitWith x (μ , xc) =
    R.lim (Regularized x μ) (regularizedWitness x μ xc)


-- Two moduli for the same sequence produce the same truncated-scale limit.  The
-- proof uses a common late index, while the truncated-scale ScaleWitness itself is
-- irrelevant.

private
  seqLimitWith-independent : ∀ x cx cy →
    seqLimitWith x cx ≡ seqLimitWith x cy
  seqLimitWith-independent x (μ , xc) (ν , yc) =
    R.eqℭ _ _ close
    where
    X = Regularized x μ
    Y = Regularized x ν
    Xc = regularizedCauchy x μ xc
    Yc = regularizedCauchy x ν yc

    close : ∀ ε →
      R.lim X ∣ Γid , Xc ∣₁ R.∼̂ᵣ[ ε ]
        R.lim Y ∣ Γid , Yc ∣₁
    close ε =
      let q = ε /4₊ /2₊
          k = ℕ.max (μ q) (ν q)
          inner = q +₊ q
          outer = q +₊ q

          xμ∼xk : x (μ q) R.∼̂ᵣ[ q ] x k
          xμ∼xk = xc q (μ q) k ℕ.≤-refl
            (ℕ.left-≤-max {m = μ q} {n = ν q})

          xk∼xν : x k R.∼̂ᵣ[ q ] x (ν q)
          xk∼xν = yc q k (ν q)
            (ℕ.right-≤-max {n = ν q} {m = μ q}) ℕ.≤-refl

          cross : X q R.∼̂ᵣ[ inner ] Y q
          cross = RP.isTriangular∼̂ᵣ _ _ _ q q xμ∼xk xk∼xν

          four-q≡ε/2 : fst ((q +₊ q) +₊ (q +₊ q)) ≡ fst (ε /2₊)
          four-q≡ε/2 =
              cong (λ z → z ℚ.+ z) (/2+/2≡id (fst (ε /4₊)))
            ∙ /4+/4≡/2 (fst ε)

          total<ε : fst (inner +₊ outer) <ℚ fst ε
          total<ε = begin<
            fst (inner +₊ outer) ≡→≤⟨ four-q≡ε/2 ⟩
            fst (ε /2₊) <⟨ /2₊<id ε ⟩
            fst ε ◾

          outer<ε : outer <₊ ε
          outer<ε = begin<
            fst outer <⟨ <₊SumRight outer inner ⟩
            fst (inner +₊ outer) <⟨ total<ε ⟩
            fst ε ◾

          Δ = <→0<Δ (fst outer) (fst ε) outer<ε
          target = (ε -₊ outer , Δ)

          inner<target : inner <₊ target
          inner<target = +CancelR< (fst inner) (fst target) (fst outer)
            (subst (fst inner ℚ.+ fst outer <ℚ_)
              (sym (minusPlus₊ ε outer)) total<ε)

          enlarged : X q R.∼̂ᵣ[ target ] Y q
          enlarged = R.isMonotone∼̂ᵣ< _ _ inner target inner<target cross
      in R.lim-lim X Γid Y Γid ε q q Xc Yc Δ enlarged

  seqLimitRec : (x : ℕ → R.ℭ̂ᵣ) →
    PT.Rec→Set {A = TargetCauchySeq x} R.ℭ̂ᵣ
  seqLimitRec x .PT.Rec→Set.isSetB = R.isSetℭ̂ᵣ
  seqLimitRec x .PT.Rec→Set.f = seqLimitWith x
  seqLimitRec x .PT.Rec→Set.fconst = seqLimitWith-independent x

  chooseSeqLimit : (x : ℕ → R.ℭ̂ᵣ) →
    ∥ TargetCauchySeq x ∥₁ → R.ℭ̂ᵣ
  chooseSeqLimit x = PT.Rec→Set.go (seqLimitRec x)

  chooseSeqLimit-β : ∀ x μ xc →
    chooseSeqLimit x ∣ μ , xc ∣₁ ≡
      R.lim (Regularized x μ) (regularizedWitness x μ xc)
  chooseSeqLimit-β x μ xc =
    PT.Rec→Set.β-go (seqLimitRec x) (μ , xc)


private
  toTruncatedScaleRec : S.Recℭ̂ₛ R.ℭ̂ᵣ
    (λ x y ε → x R.∼̂ᵣ[ ε ] y)
  toTruncatedScaleRec .S.Recℭ̂ₛ.ιA = R.ι
  toTruncatedScaleRec .S.Recℭ̂ₛ.limA = chooseSeqLimit
  toTruncatedScaleRec .S.Recℭ̂ₛ.eqA = R.eqℭ
  toTruncatedScaleRec .S.Recℭ̂ₛ.ι-ι-B = R.ι-ι
  toTruncatedScaleRec .S.Recℭ̂ₛ.ι-lim-B x y μ ε δ yc Δ inner =
    R.ι-lim x (Regularized y μ) Γid ε δ
      (regularizedCauchy y μ yc) Δ inner
  toTruncatedScaleRec .S.Recℭ̂ₛ.lim-ι-B x μ y ε δ xc Δ inner =
    R.lim-ι (Regularized x μ) Γid y ε δ
      (regularizedCauchy x μ xc) Δ inner
  toTruncatedScaleRec .S.Recℭ̂ₛ.lim-lim-B
    x μ y ν ε δ η xc yc Δ inner =
    R.lim-lim (Regularized x μ) Γid (Regularized y ν) Γid
      ε δ η
      (regularizedCauchy x μ xc) (regularizedCauchy y ν yc) Δ inner
  toTruncatedScaleRec .S.Recℭ̂ₛ.tri-B = RP.isTriangular∼̂ᵣ
  toTruncatedScaleRec .S.Recℭ̂ₛ.isPropB x y ε = R.isProp∼ x ε y


toTruncatedScale : S.ℭ̂ₛ → R.ℭ̂ᵣ
toTruncatedScale = S.Recℭ̂ₛ.go toTruncatedScaleRec

toTruncatedScale∼ : ∀ x y ε →
  x S.∼̂ₛ[ ε ] y → toTruncatedScale x R.∼̂ᵣ[ ε ] toTruncatedScale y
toTruncatedScale∼ x y ε = S.Recℭ̂ₛ.go∼ toTruncatedScaleRec

toTruncatedScale-ι : ∀ x → toTruncatedScale (S.ι x) ≡ R.ι x
toTruncatedScale-ι = S.Recℭ̂ₛ.β-go-ι toTruncatedScaleRec

toTruncatedScale-lim : ∀ x gx →
  toTruncatedScale (S.lim x gx) ≡
    chooseSeqLimit (toTruncatedScale ∘ x)
      (S.Recℭ̂ₛ.mapWitness toTruncatedScaleRec gx)
toTruncatedScale-lim = S.Recℭ̂ₛ.β-go-lim toTruncatedScaleRec


toTruncatedScale-lim-canonical : ∀ x μ xc →
  toTruncatedScale (S.lim x ∣ μ , xc ∣₁) ≡
    R.lim (λ ε → toTruncatedScale (x (μ ε)))
      ∣ Γid , regularizedCauchy (toTruncatedScale ∘ x) μ
        (λ ε m n με≤m με≤n →
          toTruncatedScale∼ (x m) (x n) ε
            (xc ε m n με≤m με≤n)) ∣₁
toTruncatedScale-lim-canonical x μ xc =
    toTruncatedScale-lim x ∣ μ , xc ∣₁
  ∙ chooseSeqLimit-β (toTruncatedScale ∘ x) μ
      (λ ε m n με≤m με≤n →
        toTruncatedScale∼ (x m) (x n) ε
          (xc ε m n με≤m με≤n))


regularizedFamilyCauchy : ∀ (x : ℕ → R.ℭ̂ᵣ) μ
  → (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
      x m R.∼̂ᵣ[ ε ] x n)
  → ∀ ε δ → x (μ ε) R.∼̂ᵣ[ ε +₊ δ ] x (μ δ)
regularizedFamilyCauchy = regularizedCauchy
