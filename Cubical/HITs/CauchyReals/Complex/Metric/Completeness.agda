module Cubical.HITs.CauchyReals.Complex.Metric.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using
  (𝕣-lim-self)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Coordinates


private
  module ℂP = PremetricTheory ℂPremetricSpace


opaque
  reCauchy : (x : ℚ₊ → ℂ) → ℂP.isCauchy x →
    ∀ ε δ → re (x ε) ∼[ ε +₊ δ ] re (x δ)
  reCauchy x xc ε δ = ≈ℝ→∼ (re (x ε)) (re (x δ)) (ε +₊ δ)
    (re-pres≈ (x ε) (x δ) (ε +₊ δ) (xc ε δ))


opaque
  imCauchy : (x : ℚ₊ → ℂ) → ℂP.isCauchy x →
    ∀ ε δ → im (x ε) ∼[ ε +₊ δ ] im (x δ)
  imCauchy x xc ε δ = ≈ℝ→∼ (im (x ε)) (im (x δ)) (ε +₊ δ)
    (im-pres≈ (x ε) (x δ) (ε +₊ δ) (xc ε δ))


reLimit : (x : ℚ₊ → ℂ) → ℂP.isCauchy x → ℝ
reLimit x xc = lim (re ∘ x) (reCauchy x xc)


imLimit : (x : ℚ₊ → ℂ) → ℂP.isCauchy x → ℝ
imLimit x xc = lim (im ∘ x) (imCauchy x xc)


complexLimit : (x : ℚ₊ → ℂ) → ℂP.isCauchy x → ℂ
complexLimit x xc = reLimit x xc , imLimit x xc


opaque
  re-difference-path : ∀ z w → re (z -ℂ w) ≡ re z -ᵣ re w
  re-difference-path _ _ = refl


opaque
  im-difference-path : ∀ z w → im (z -ℂ w) ≡ im z -ᵣ im w
  im-difference-path _ _ = refl


opaque
  coordinateLimitClose : ∀ x (xc : ℂP.isCauchy x) δ η →
    x δ ≈ℂ[ (δ +₊ η) +₊ (δ +₊ η) ] complexLimit x xc
  coordinateLimitClose x xc δ η =
    let rlim = reLimit x xc
        ilim = imLimit x xc
        θ = δ +₊ η
        reClose : absᵣ (re (x δ) -ᵣ rlim) <ᵣ rat (fst θ)
        reClose = fst (∼≃abs<ε (re (x δ)) rlim θ)
          (𝕣-lim-self (re ∘ x) (reCauchy x xc) δ η)
        imClose : absᵣ (im (x δ) -ᵣ ilim) <ᵣ rat (fst θ)
        imClose = fst (∼≃abs<ε (im (x δ)) ilim θ)
          (𝕣-lim-self (im ∘ x) (imCauchy x xc) δ η)
        coordinateBound :
          modulus (x δ -ℂ complexLimit x xc) ≤ᵣ
          absᵣ (re (x δ) -ᵣ rlim) +ᵣ
          absᵣ (im (x δ) -ᵣ ilim)
        coordinateBound = isTrans≤≡ᵣ _ _ _
          (modulus≤abs-coordinates (x δ -ℂ complexLimit x xc))
          (cong₂ _+ᵣ_
            (cong absᵣ (re-difference-path (x δ) (complexLimit x xc)))
            (cong absᵣ (im-difference-path (x δ) (complexLimit x xc))))
        coordinateSumClose :
          absᵣ (re (x δ) -ᵣ rlim) +ᵣ
          absᵣ (im (x δ) -ᵣ ilim) <ᵣ
          rat (fst (θ +₊ θ))
        coordinateSumClose = subst
          (absᵣ (re (x δ) -ᵣ rlim) +ᵣ
            absᵣ (im (x δ) -ᵣ ilim) <ᵣ_)
          (+ᵣ-rat (fst θ) (fst θ))
          (<ᵣMonotone+ᵣ _ _ _ _ reClose imClose)
    in isTrans≤<ᵣ _ _ _ coordinateBound coordinateSumClose


opaque
  complexLimitIsLimit : ∀ x (xc : ℂP.isCauchy x) →
    ℂP.isLimit x (complexLimit x xc)
  complexLimitIsLimit x xc ε θ =
    let δ = ((θ /2₊) /2₊) /2₊
        near : x ε ≈ℂ[ (ε +₊ δ) +₊ ((δ +₊ δ) +₊ (δ +₊ δ)) ]
          complexLimit x xc
        near = PremetricStr.isTriangular≈ (snd ℂPremetricSpace)
          (x ε) (x δ) (complexLimit x xc)
          (ε +₊ δ) ((δ +₊ δ) +₊ (δ +₊ δ))
          (xc ε δ) (coordinateLimitClose x xc δ δ)
    in PremetricStr.isMonotone≈< (snd ℂPremetricSpace)
        (x ε) (complexLimit x xc)
        ((ε +₊ δ) +₊ ((δ +₊ δ) +₊ (δ +₊ δ)))
        (ε +₊ θ) <≤ℚ! near


isCompleteℂ : ℂP.isComplete
isCompleteℂ x xc = complexLimit x xc , complexLimitIsLimit x xc
