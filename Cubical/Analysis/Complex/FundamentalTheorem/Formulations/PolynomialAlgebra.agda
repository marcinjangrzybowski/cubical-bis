module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra where

-- Only definitions of certificates. Keeping their coefficient expressions
-- generic prevents projection checking from expanding completed arithmetic.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Algebra.CommRing
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as MonicDifferentialDefinition

module Certificates {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open PolynomialDefinition.Polynomials R
  open MonicDefinition.Monic R
  open DifferentialDefinition.Differential R
  open MonicDifferentialDefinition.MonicDifferential R
  private A = fst R

  coefficient : List A → ℕ → A
  coefficient [] k = 0r
  coefficient (a ∷ p) zero = a
  coefficient (a ∷ p) (suc k) = coefficient p k

  PolynomialIdentity : List A → List A → Type ℓ
  PolynomialIdentity p q = ∀ k → coefficient p k ≡ coefficient q k

  record BezoutSeparability {n : ℕ} (p : MonicPolynomial n) : Type ℓ where
    field
      bezoutS bezoutT : List A
      bezoutIdentity : PolynomialIdentity
        (addCoefficients
          (multiplyCoefficients bezoutS (monicCoefficients p))
          (multiplyCoefficients bezoutT (differentiate (monicCoefficients p))))
        (1r ∷ [])
