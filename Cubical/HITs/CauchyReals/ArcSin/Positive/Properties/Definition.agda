module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (riemannSum-empty)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core
arcSin : ∀ x → (x∈ : x ∈ pred≤< 0 1) → ℝ
arcSin x x∈ = fst (arcSinDef x x∈)

emptyIntegral : ∀ x f → (on[ x , x ]IntegralOf f is 0 )
emptyIntegral x f ε = ∣ 1 ,
  (λ (_ , tp) _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (Rℝ.+InvR' _ _ (sym (riemannSum-empty tp (uncurry ∘ f) refl)) )
     ∙ absᵣ0)
    (snd (ℚ₊→ℝ₊ ε))) ∣₁

arcSin[0]≡0 : (0∈ : 0 ∈ pred≤< 0 1) → arcSin 0 0∈ ≡ 0
arcSin[0]≡0 0∈ = IntegralUniq 0 0 (fst 0∈) _ _ _
  (snd (arcSinDef 0 0∈)) (emptyIntegral 0 _)
