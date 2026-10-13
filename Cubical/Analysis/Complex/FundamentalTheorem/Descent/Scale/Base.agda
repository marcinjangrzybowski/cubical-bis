module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Scale.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot

BalancedPowerScale : ∀ {n} → Vec ℝ n → (Fin n → ℕ) → ℝ → ℚ₊ → Type₀
BalancedPowerScale {n} coefficients degrees target ε =
  Σ[ radius ∈ ℝ ] (0ℝ <ℝ radius) × (Σ[ index ∈ Fin n ]
    (weightedPower (lookup index coefficients) (degrees index) radius ≡ target) ×
    (∀ i → weightedPower (lookup i coefficients) (degrees i) radius <ℝ target + rat (fst ε)))

balancedScale : ∀ {n} {coefficients : Vec ℝ n} {degrees : Fin n → ℕ} {target : ℝ} {ε : ℚ₊} (radius : ℝ) →
  0ℝ <ℝ radius → (index : Fin n) →
  weightedPower (lookup index coefficients) (degrees index) radius ≡ target →
  (∀ i → weightedPower (lookup i coefficients) (degrees i) radius <ℝ target + rat (fst ε)) →
  BalancedPowerScale coefficients degrees target ε
balancedScale radius positive index selected bounded = radius , positive , index , selected , bounded

slackAbove : (target : ℝ) (ε : ℚ₊) → target <ℝ target + rat (fst ε)
slackAbove target ε = subst (_<ℝ target + rat (fst ε)) (addIdR target)
    (<ℝ-addL 0ℝ (rat (fst ε)) target (<ℚ→<ℝ 0 (fst ε) (snd ε)))

opaque
  replaceBelow : ∀ x y z → x ≡ y → y <ℝ z → x <ℝ z
  replaceBelow x y z equation below = subst (_<ℝ z) (sym equation) below
