module Cubical.Analysis.Complex.Polynomial.Monic.FactorsAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Factors {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open MonicDefinition.Monic R
  private A = fst R

  remainingProduct : ∀ {n} → Vec A n → Fin n → A → A
  remainingProduct (r ∷ roots) zero z = productOfLinearFactors roots z
  remainingProduct (r ∷ roots) (suc i) z = (z - r) · remainingProduct roots i z

  private
    swap : ∀ a b c → a · (b · c) ≡ b · (a · c)
    swap a b c = solve! R

  product-factor : ∀ {n} (roots : Vec A n) i z →
    productOfLinearFactors roots z ≡ (z - lookup i roots) · remainingProduct roots i z
  product-factor (r ∷ roots) zero z = refl
  product-factor (r ∷ roots) (suc i) z = cong ((z - r) ·_) (product-factor roots i z)
    ∙ swap (z - r) (z - lookup i roots) (remainingProduct roots i z)

  opposite : ∀ z w → z - w ≡ - (w - z)
  opposite z w = solve! R
