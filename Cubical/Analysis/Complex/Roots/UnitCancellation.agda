module Cubical.Analysis.Complex.Roots.UnitCancellation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.NormSquared
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Roots.Existence
import Cubical.Analysis.Complex.Roots.UnitCancellationAlgebra as AlgebraDefinition

private
  module A = AlgebraDefinition.UnitCancellation ℂCommRing

-- A unit nth power can put any two unit coefficients in opposite
-- directions. This is the angular part of polynomial descent.
oppositeUnitPower : ∀ n a b → modulusℂ a ≡ 1ℝ → modulusℂ b ≡ 1ℝ →
  ∥ Σ[ u ∈ ℂ ] (modulusℂ u ≡ 1ℝ) × (a +ℂ (b ·ℂ (u ^ℂ suc n)) ≡ 0ℂ) ∥₁
oppositeUnitPower n a b a-unit b-unit = PT.map
  (λ (u , power , unit) → u , unit , cong (λ t → a +ℂ (b ·ℂ t)) power
    ∙ A.cancelUnit a b (conjugate b) inverse)
  (unitComplexRoot n direction direction-unit)
  where
  direction : ℂ
  direction = (-ℂ a) ·ℂ conjugate b

  direction-unit : modulusℂ direction ≡ 1ℝ
  direction-unit = modulusℂ-mul (-ℂ a) (conjugate b)
    ∙ cong₂ _·_ (modulusℂ-neg a ∙ a-unit) (modulusℂ-conjugate b ∙ b-unit)
    ∙ mulIdR 1ℝ

  inverse : b ·ℂ conjugate b ≡ 1ℂ
  inverse = mul-conjugate b ∙ cong fromℝ
    (sym (modulusℂ-square b) ∙ cong (λ r → r · r) b-unit ∙ mulIdR 1ℝ)
