module Cubical.Analysis.Real.Functions.SquareRoot.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located

squarePres<Nonnegative : ∀ x y → 0ℝ ≤ℝ x → x <ℝ y → x · x <ℝ y · y
squarePres<Nonnegative x y nonnegative less =
  ≤<ℝ-trans (x · x) (x · y) (y · y)
    (mulPres≤L x y x (0≤→isNonnegative x nonnegative) (<ℝ-weaken x y less))
    (mulPres<PosR x y y (≤<ℝ-trans 0ℝ x y nonnegative less) less)

squareReflects≤Nonnegative : ∀ x y → 0ℝ ≤ℝ y → x · x ≤ℝ y · y → x ≤ℝ y
squareReflects≤Nonnegative x y nonnegative squares = notGreater→≤ℝ x y λ less →
  ≤ℝ→≯ (x · x) (y · y) squares (squarePres<Nonnegative y x nonnegative less)

squareInjectiveNonnegative : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → x · x ≡ y · y → x ≡ y
squareInjectiveNonnegative x y xp yp equal = ≤ℝ-antisym x y
  (squareReflects≤Nonnegative x y yp (subst (_≤ℝ y · y) (sym equal) (≤ℝ-refl (y · y))))
  (squareReflects≤Nonnegative y x xp (subst (_≤ℝ x · x) equal (≤ℝ-refl (x · x))))
