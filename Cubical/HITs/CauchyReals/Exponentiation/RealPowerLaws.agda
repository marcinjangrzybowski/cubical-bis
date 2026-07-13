module Cubical.HITs.CauchyReals.Exponentiation.RealPowerLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.ExponentiationMore
  using (_^ᵣ_; ^ᵣ+)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

opaque
  -- Previous name: factor-xᵃ-xᵇ'ᵣ.
  realPowerDifferenceFactor : ∀ x a b →
    fst (x ^ᵣ a) -ᵣ fst (x ^ᵣ b) ≡
      fst (x ^ᵣ a) ·ᵣ (1 -ᵣ fst (x ^ᵣ (b -ᵣ a)))
  realPowerDifferenceFactor x a b =
    cong₂ _-ᵣ_ (sym (·IdR _))
      (cong fst
        (cong (x ^ᵣ_) (sym ℝ!)
        ∙ ^ᵣ+ x a (b -ᵣ a)))
    ∙ sym (·DistL- _ _ _)
