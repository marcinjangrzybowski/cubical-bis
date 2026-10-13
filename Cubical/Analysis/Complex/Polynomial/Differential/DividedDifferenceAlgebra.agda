module Cubical.Analysis.Complex.Polynomial.Differential.DividedDifferenceAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition

module DividedDifferenceIdentities {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open PolynomialDefinition.Polynomials R
  open DifferentialDefinition.Differential R

  errorStep : ∀ a p r w z →
    evaluate (quotientAt (a ∷ p) w) z - derivativeValue (a ∷ p) r ≡
    (evaluate p w - evaluate p r) +
      ((z - r) · evaluate (quotientAt p w) z +
        r · (evaluate (quotientAt p w) z - derivativeValue p r))
  errorStep a p r w z = solve! R

  private
    factorStep : ∀ v d z w q →
      ((v + (z - w) · q) - v) - d · (z - w) ≡ (z - w) · (q - d)
    factorStep v d z w q = solve! R

  -- Subtraction of the derivative leaves a product by the displacement.
  -- This identity has no division by z-w, including on the diagonal.
  remainderFactor : ∀ p r z w →
    (evaluate p z - evaluate p w) - derivativeValue p r · (z - w) ≡
    (z - w) · (evaluate (quotientAt p w) z - derivativeValue p r)
  remainderFactor p r z w =
    cong (λ v → (v - evaluate p w) - derivativeValue p r · (z - w))
      (divisionIdentity p w z)
    ∙ factorStep (evaluate p w) (derivativeValue p r) z w (evaluate (quotientAt p w) z)

  boundStep : ∀ lip radius bound distance →
    lip · distance + (distance · lip + radius · (bound · distance)) ≡
    (lip + (lip + radius · bound)) · distance
  boundStep lip radius bound distance = solve! R

  recover : ∀ z r → z ≡ (z - r) + r
  recover z r = solve! R
