module Cubical.Analysis.Real.Functions.SquareRoot.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base using ([_/_]; eq/)
open import Cubical.Data.Nat.Literals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition

private
  half : ℝ
  half = rat [ pos 1 / 1+ 1 ]

  twice-half : half + half ≡ 1ℝ
  twice-half = rat+rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl)

  halfScaleDouble : ∀ x → half · x + half · x ≡ x
  halfScaleDouble x = sym (mulDistL half half x) ∙ cong (_· x) twice-half ∙ mulIdL x

-- The already constructed global logarithm gives positive square roots.
-- Zero is intentionally outside this domain; no case split on arbitrary
-- real equality is used to extend this definition.
opaque
  positiveSqrtℝ : (x : ℝ) → 0ℝ <ℝ x → ℝ
  positiveSqrtℝ x positive = expℝ (half · logℝ (x , positive))

  positiveSqrtℝ-positive : ∀ x positive → 0ℝ <ℝ positiveSqrtℝ x positive
  positiveSqrtℝ-positive x positive = expℝ-positive (half · logℝ (x , positive))

  positiveSqrtℝ-square : ∀ x positive → positiveSqrtℝ x positive · positiveSqrtℝ x positive ≡ x
  positiveSqrtℝ-square x positive =
    sym (exponentialEntireValue-add (half · logℝ (x , positive)) (half · logℝ (x , positive)))
    ∙ cong expℝ (halfScaleDouble (logℝ (x , positive))) ∙ expℝ-logℝ (x , positive)

positiveSqrtℝ-unique : ∀ x positive y → 0ℝ ≤ℝ y → y · y ≡ x → y ≡ positiveSqrtℝ x positive
positiveSqrtℝ-unique x positive y nonnegative square = squareInjectiveNonnegative
  y (positiveSqrtℝ x positive) nonnegative
  (<ℝ-weaken 0ℝ (positiveSqrtℝ x positive) (positiveSqrtℝ-positive x positive))
  (square ∙ sym (positiveSqrtℝ-square x positive))
