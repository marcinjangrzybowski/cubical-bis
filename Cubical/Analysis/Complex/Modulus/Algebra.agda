module Cubical.Analysis.Complex.Modulus.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Cartesian as CartesianDefinition
import Cubical.Analysis.Complex.Algebra.Conjugation as ConjugationDefinition

module ModulusAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open CartesianDefinition.Cartesian R
  open ConjugationDefinition.Conjugation R

  normSq-add : ∀ z w → normSq (z +ℂ w) ≡
    (normSq z + normSq w) +
      (fst (z ·ℂ conjugate w) + fst (z ·ℂ conjugate w))
  normSq-add (a , b) (c , d) = solve! R

  squareSumExpansion : ∀ x y → (x + y) · (x + y) ≡
    (x · x + y · y) + (x · y + x · y)
  squareSumExpansion x y = solve! R

  productSquare : ∀ x y → (x · y) · (x · y) ≡ (x · x) · (y · y)
  productSquare x y = solve! R
