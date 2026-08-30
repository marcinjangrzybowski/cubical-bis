module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; [] ; _∷_)

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence


private
  zeroℝ : Real.ℝ
  zeroℝ = CommRingStr.0r (snd ℝCommRing)


-- Fixed polynomials preserve the radiuswise Cauchy condition directly.
-- Recursion uses only constant, product, and sum preservation, so every
-- radius opens finitely many truncated tails and never constructs a global
-- modulus.

polynomialPresIsCauchySequence : ∀ coefficients {x} →
  IsCauchySequence x →
  IsCauchySequence (evaluatePolynomial coefficients ∘ x)
polynomialPresIsCauchySequence [] {x} gx =
  constantIsCauchySequence zeroℝ
polynomialPresIsCauchySequence (a ∷ coefficients) {x} gx =
  addPresIsCauchySequence
    (constantIsCauchySequence a)
    (mulPresIsCauchySequence gx
      (polynomialPresIsCauchySequence coefficients gx))


polynomialPresIsLimitSequence : ∀ coefficients {x l} →
  isLimitSequence x l →
  isLimitSequence
    (evaluatePolynomial coefficients ∘ x)
    (evaluatePolynomial coefficients l)
polynomialPresIsLimitSequence [] {x} {l} x→l =
  constantIsLimitSequence zeroℝ
polynomialPresIsLimitSequence
    (a ∷ coefficients) {x} {l} x→l =
  addPresIsLimitSequence
    (constantIsLimitSequence a)
    (mulPresIsLimitSequence x→l
      (polynomialPresIsLimitSequence coefficients x→l))
