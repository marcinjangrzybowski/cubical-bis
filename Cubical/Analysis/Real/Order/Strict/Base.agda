module Cubical.Analysis.Real.Order.Strict.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance

open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)

open ℚInstance.PositiveRationals using (ℚ₊)


GapBound : ℝ → ℝ → ℚ₊ → Type₀
GapBound x y δ = x + rat (fst δ) ≤ℝ y

PositiveGap : ℝ → ℝ → Type₀
PositiveGap x y = Σ[ δ ∈ ℚ₊ ] GapBound x y δ

positiveGap : ∀ {x y : ℝ} (δ : ℚ₊) → GapBound x y δ → PositiveGap x y
positiveGap {x} {y} δ p = δ , p

width : ∀ {x y : ℝ} → PositiveGap x y → ℚ₊
width {x} {y} w = fst w

bound : ∀ {x y : ℝ} (w : PositiveGap x y) → GapBound x y (fst w)
bound {x} {y} w = snd w

infix 4 _<ℝ_

_<ℝ_ : ℝ → ℝ → Type₀
x <ℝ y = ∥ PositiveGap x y ∥₁

isProp<ℝ : ∀ x y → isProp (x <ℝ y)
isProp<ℝ _ _ = squash₁
