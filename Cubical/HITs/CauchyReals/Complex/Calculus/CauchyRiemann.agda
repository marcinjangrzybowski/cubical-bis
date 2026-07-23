module Cubical.HITs.CauchyReals.Complex.Calculus.CauchyRiemann where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


realJacobian : ℝ → ℝ → ℝ → ℝ → ℂ → ℂ
realJacobian uₓ uᵧ vₓ vᵧ (h , k) =
  (uₓ ·ᵣ h +ᵣ uᵧ ·ᵣ k) ,
  (vₓ ·ᵣ h +ᵣ vᵧ ·ᵣ k)


CauchyRiemann : ℝ → ℝ → ℝ → ℝ → Type₀
CauchyRiemann uₓ uᵧ vₓ vᵧ =
  (uₓ ≡ vᵧ) × (uᵧ ≡ -ᵣ vₓ)


IsComplexLinearJacobian : ℝ → ℝ → ℝ → ℝ → Type₀
IsComplexLinearJacobian uₓ uᵧ vₓ vᵧ =
  Σ[ derivative ∈ ℂ ]
    ((h : ℂ) →
      realJacobian uₓ uᵧ vₓ vᵧ h ≡ derivative ·ℂ h)


cauchyRiemann→complexLinear : ∀ uₓ uᵧ vₓ vᵧ →
  CauchyRiemann uₓ uᵧ vₓ vᵧ →
  IsComplexLinearJacobian uₓ uᵧ vₓ vᵧ
cauchyRiemann→complexLinear uₓ uᵧ vₓ vᵧ
  (uₓ≡vᵧ , uᵧ≡-vₓ) =
  (uₓ , vₓ) , λ (h , k) → ℂ≡
    (cong (λ r → uₓ ·ᵣ h +ᵣ r ·ᵣ k) uᵧ≡-vₓ ∙ ℝ!)
    (cong (λ r → vₓ ·ᵣ h +ᵣ r ·ᵣ k) (sym uₓ≡vᵧ) ∙ ℝ!)


complexLinear→cauchyRiemann : ∀ uₓ uᵧ vₓ vᵧ →
  IsComplexLinearJacobian uₓ uᵧ vₓ vᵧ →
  CauchyRiemann uₓ uᵧ vₓ vᵧ
complexLinear→cauchyRiemann uₓ uᵧ vₓ vᵧ
  (derivative , linear) =
  (uₓ≡re-derivative ∙ sym (vᵧ≡re-derivative)) ,
  (uᵧ≡-im-derivative ∙ cong -ᵣ_ (sym vₓ≡im-derivative))
  where
  uₓ≡re-derivative : uₓ ≡ re derivative
  uₓ≡re-derivative =
    ℝ! ∙ cong re (linear 1ℂ) ∙ ℝ!

  vₓ≡im-derivative : vₓ ≡ im derivative
  vₓ≡im-derivative =
    ℝ! ∙ cong im (linear 1ℂ) ∙ ℝ!

  uᵧ≡-im-derivative : uᵧ ≡ -ᵣ im derivative
  uᵧ≡-im-derivative =
    ℝ! ∙ cong re (linear iℂ) ∙ ℝ!

  vᵧ≡re-derivative : vᵧ ≡ re derivative
  vᵧ≡re-derivative =
    ℝ! ∙ cong im (linear iℂ) ∙ ℝ!


complexLinearJacobianDerivative : ∀ uₓ uᵧ vₓ vᵧ →
  CauchyRiemann uₓ uᵧ vₓ vᵧ → ℂ
complexLinearJacobianDerivative uₓ uᵧ vₓ vᵧ _ = uₓ , vₓ


complexLinearJacobianAction : ∀ uₓ uᵧ vₓ vᵧ
  (cr : CauchyRiemann uₓ uᵧ vₓ vᵧ) h →
  realJacobian uₓ uᵧ vₓ vᵧ h ≡
  complexLinearJacobianDerivative uₓ uᵧ vₓ vᵧ cr ·ℂ h
complexLinearJacobianAction uₓ uᵧ vₓ vᵧ cr =
  snd (cauchyRiemann→complexLinear uₓ uᵧ vₓ vᵧ cr)
