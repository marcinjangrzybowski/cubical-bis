module Cubical.HITs.CauchyReals.Foundation.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using (lim-surj)

CauchyPresentation : Type
CauchyPresentation =
  Σ[ x ∈ (ℚ₊ → ℝ) ]
    ∀ δ ε → x δ ∼[ δ +₊ ε ] x ε

presentationLim : CauchyPresentation → ℝ
presentationLim = uncurry lim

opaque
  -- HoTT Book, Lemma 11.3.11.
  cauchyRealUniversalProperty :
    ∀ {ℓ} (A : Type ℓ) (isSetA : isSet A)
    (f : CauchyPresentation → A) →
    (∀ u v → presentationLim u ≡ presentationLim v → f u ≡ f v) →
    ∃![ g ∈ (ℝ → A) ] f ≡ g ∘ presentationLim
  cauchyRealUniversalProperty {ℓ = ℓ} A isSetA f respects =
    center , unique
    where
    Factorization : Type ℓ
    Factorization =
      Σ[ g ∈ (ℝ → A) ] f ≡ g ∘ presentationLim

    Choice : ℝ → Type
    Choice r = Σ[ u ∈ CauchyPresentation ] r ≡ presentationLim u

    choiceValue : ∀ r → Choice r → A
    choiceValue _ = f ∘ fst

    choiceValueConstant : ∀ r → 2-Constant (choiceValue r)
    choiceValueConstant r (u , r≡u) (v , r≡v) =
      respects u v (sym r≡u ∙ r≡v)

    choose : ∀ r → ∥ Choice r ∥₁ → A
    choose r = PT.rec→Set isSetA (choiceValue r) (choiceValueConstant r)

    factor : ℝ → A
    factor r = choose r (lim-surj r)

    factors : f ≡ factor ∘ presentationLim
    factors = funExt λ u →
      cong (choose (presentationLim u))
        (squash₁ ∣ u , refl ∣₁ (lim-surj (presentationLim u)))

    center : Factorization
    center = factor , factors

    factorUnique : ∀ (g : ℝ → A) →
      f ≡ g ∘ presentationLim → factor ≡ g
    factorUnique g gFactors = funExt λ r →
      PT.rec
        (isSetA (factor r) (g r))
        (λ (u , r≡u) →
          cong factor r≡u
          ∙ sym (funExt⁻ factors u)
          ∙ funExt⁻ gFactors u
          ∙ cong g (sym r≡u))
        (lim-surj r)

    unique : ∀ h → center ≡ h
    unique (g , gFactors) =
      Σ≡Prop
        (λ h → isSetΠ (λ _ → isSetA) f (h ∘ presentationLim))
        (factorUnique g gFactors)
