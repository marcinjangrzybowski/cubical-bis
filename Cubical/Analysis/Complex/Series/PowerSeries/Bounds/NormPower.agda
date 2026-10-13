module Cubical.Analysis.Complex.Series.PowerSeries.Bounds.NormPower where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤L)
open import Cubical.Analysis.Real.Functions.Powers

-- Abstract the ring and size map before induction. Instantiating afterwards
-- keeps the complex coordinate arithmetic out of native-real order checking.
module NormPower {ℓ} (R : CommRing ℓ) (size : fst R → ℝ)
  (unit : size (CommRingStr.1r (snd R)) ≡ 1ℝ)
  (nonnegative : ∀ z → 0ℝ ≤ℝ size z)
  (product : ∀ z w → size (CommRingStr._·_ (snd R) z w) ≤ℝ size z · size w) where
  private module C = CommRingStr (snd R)
  private module P = Exponentiation R

  opaque
    powerBound : ∀ z n → size (z P.^ n) ≤ℝ powℝ (size z) n
    powerBound z zero = subst (_≤ℝ 1ℝ) (sym unit) (≤ℝ-refl 1ℝ)
    powerBound z (suc n) = ≤ℝ-trans (size (z C.· (z P.^ n)))
      (size z · size (z P.^ n)) (size z · powℝ (size z) n)
      (product z (z P.^ n))
      (mulPres≤L (size (z P.^ n)) (powℝ (size z) n) (size z)
        (0≤→isNonnegative (size z) (nonnegative z)) (powerBound z n))
