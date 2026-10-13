module Cubical.Analysis.Complex.Roots.Cancellation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Normalize
open import Cubical.Analysis.Complex.Roots.UnitCancellation
import Cubical.Analysis.Complex.Roots.UnitCancellationAlgebra as AlgebraDefinition

private
  module A = AlgebraDefinition.UnitCancellation ℂCommRing

  fromℝSubtract : ∀ x y → fromℝ x -ℂ fromℝ y ≡ fromℝ (x - y)
  fromℝSubtract x y = ℂ≡ refl (subSelf 0ℝ)

-- The optimal two-term cancellation, at any nonzero natural degree.
-- Both coefficients are supplied apart from zero; the direction is only
-- asserted to exist under truncation.
oppositeCoefficientPower : ∀ n a b → 0ℝ <ℝ modulusℂ a → 0ℝ <ℝ modulusℂ b →
  ∥ Σ[ u ∈ ℂ ] (modulusℂ u ≡ 1ℝ) ×
    (modulusℂ (a +ℂ (b ·ℂ (u ^ℂ suc n))) ≡ absℝ (modulusℂ a - modulusℂ b)) ∥₁
oppositeCoefficientPower n a b a-positive b-positive = PT.map fromUnit
  (oppositeUnitPower n (normalizeℂ a a-positive) (normalizeℂ b b-positive)
    (modulusℂ-normalize a a-positive) (modulusℂ-normalize b b-positive))
  where
  fromUnit : (Σ[ u ∈ ℂ ] (modulusℂ u ≡ 1ℝ) ×
      (normalizeℂ a a-positive +ℂ (normalizeℂ b b-positive ·ℂ (u ^ℂ suc n)) ≡ 0ℂ)) →
    Σ[ u ∈ ℂ ] (modulusℂ u ≡ 1ℝ) ×
      (modulusℂ (a +ℂ (b ·ℂ (u ^ℂ suc n))) ≡ absℝ (modulusℂ a - modulusℂ b))
  fromUnit (u , unit , cancel) = u , unit , cong modulusℂ equation
    ∙ modulusℂ-mul (fromℝ (modulusℂ a - modulusℂ b)) (normalizeℂ a a-positive)
    ∙ cong₂ _·_ (modulusℂ-fromℝ (modulusℂ a - modulusℂ b)) (modulusℂ-normalize a a-positive)
    ∙ mulIdR (absℝ (modulusℂ a - modulusℂ b))
    where
    equation : a +ℂ (b ·ℂ (u ^ℂ suc n)) ≡
      fromℝ (modulusℂ a - modulusℂ b) ·ℂ normalizeℂ a a-positive
    equation = cong₂ _+ℂ_ (sym (normalizeℂ-reconstruct a a-positive))
      (cong (_·ℂ (u ^ℂ suc n)) (sym (normalizeℂ-reconstruct b b-positive))
        ∙ sym (·ℂAssoc (fromℝ (modulusℂ b)) (normalizeℂ b b-positive) (u ^ℂ suc n)))
      ∙ A.oppositeScaled (fromℝ (modulusℂ a)) (fromℝ (modulusℂ b))
        (normalizeℂ a a-positive) (normalizeℂ b b-positive) (u ^ℂ suc n) cancel
      ∙ cong (_·ℂ normalizeℂ a a-positive) (fromℝSubtract (modulusℂ a) (modulusℂ b))
