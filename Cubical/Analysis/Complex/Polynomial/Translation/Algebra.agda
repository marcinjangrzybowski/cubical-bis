module Cubical.Analysis.Complex.Polynomial.Translation.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Translation {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open MonicDefinition.Monic R

  -- Horner translation preserves the formal degree and its leading one.
  -- No test that a coefficient vanishes is involved.
  translateMonic : ∀ {n} → MonicPolynomial n → fst R → MonicPolynomial n
  translateMonic [] center = []
  translateMonic (a ∷ p) center = addConstant a (multiplyLinear (- center) (translateMonic p center))

  evaluate-translateMonic : ∀ {n} (p : MonicPolynomial n) center z →
    evaluateMonic (translateMonic p center) z ≡ evaluateMonic p (center + z)
  evaluate-translateMonic [] center z = refl
  evaluate-translateMonic (a ∷ p) center z =
    evaluate-addConstant a (multiplyLinear (- center) (translateMonic p center)) z
      ∙ cong (a +_) (evaluate-multiplyLinear (- center) (translateMonic p center) z)
      ∙ cong (λ u → a + (z - (- center)) · u) (evaluate-translateMonic p center z)
      ∙ cong (λ u → a + u · evaluateMonic p (center + z)) (solve! R)

  translateMonic-atZero : ∀ {n} (p : MonicPolynomial n) center →
    evaluateMonic (translateMonic p center) 0r ≡ evaluateMonic p center
  translateMonic-atZero p center = evaluate-translateMonic p center 0r
    ∙ cong (evaluateMonic p) (+IdR center)
