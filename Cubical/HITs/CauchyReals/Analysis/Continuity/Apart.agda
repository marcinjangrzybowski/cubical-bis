module Cubical.HITs.CauchyReals.Analysis.Continuity.Apart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals

private
  opaque
    rationalZeroOrApart : ∀ q → (0 ≡ q) ⊎ (0 ℚ.# q)
    rationalZeroOrApart = ℚ.≡⊎# 0

    rationalZeroOrApart-rec : ∀ {ℓ} {A : Type ℓ} q →
      (0 ≡ q → A) → (0 ℚ.# q → A) → A
    rationalZeroOrApart-rec q zeroCase apartCase =
      ⊎.rec zeroCase apartCase (rationalZeroOrApart q)

opaque
  ≤ContinuousAwayFromZero : ∀ {f g : ℝ → ℝ} →
    IsContinuous f → IsContinuous g →
    f 0 ≤ᵣ g 0 →
    (∀ r → 0 ＃ r → f r ≤ᵣ g r) →
    ∀ r → f r ≤ᵣ g r
  ≤ContinuousAwayFromZero {f} {g} fCont gCont atZero away =
    ≤Cont fCont gCont λ q →
      rationalZeroOrApart-rec q
        (λ 0≡q →
          subst2 _≤ᵣ_
            (cong (f ∘ rat) 0≡q)
            (cong (g ∘ rat) 0≡q)
            atZero)
        (λ 0#q →
          away (rat q)
            (⊎.map (λ 0<q → <ℚ→<ᵣ 0 q 0<q)
                   (λ q<0 → <ℚ→<ᵣ q 0 q<0) 0#q))
