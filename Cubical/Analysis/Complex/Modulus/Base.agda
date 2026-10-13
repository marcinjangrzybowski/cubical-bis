module Cubical.Analysis.Complex.Modulus.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Functions.SquareRoot.Estimates
open import Cubical.Analysis.Real.Functions.SquareRoot.Nonnegative
open import Cubical.Analysis.Real.Functions.SquareRoot.Laws
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.NormSquared
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  -- Transport the nonnegativity certificate along a radicand equality.
  -- The square-root laws themselves come from the native real API.
  sqrt-cong : ∀ {x y} xp yp → x ≡ y →
    nonnegativeSqrtℝ x xp ≡ nonnegativeSqrtℝ y yp
  sqrt-cong xp yp equal = cong (λ x → nonnegativeSqrtℝ (fst x) (snd x))
    (Σ≡Prop (isProp≤ℝ 0ℝ) {u = _ , xp} {v = _ , yp} equal)

opaque
  -- The Euclidean modulus complements the l1 norm used for completion and
  -- contraction estimates. In particular, this modulus is multiplicative.
  modulusℂ : ℂ → ℝ
  modulusℂ z = nonnegativeSqrtℝ (normSq z) (normSq-nonnegative z)

  modulusℂ-nonnegative : ∀ z → 0ℝ ≤ℝ modulusℂ z
  modulusℂ-nonnegative z = nonnegativeSqrtℝ-nonnegative (normSq z) (normSq-nonnegative z)

  modulusℂ-square : ∀ z → modulusℂ z · modulusℂ z ≡ normSq z
  modulusℂ-square z = nonnegativeSqrtℝ-square (normSq z) (normSq-nonnegative z)


opaque
  unfolding modulusℂ

  modulusℂ-unique : ∀ z r → 0ℝ ≤ℝ r → r · r ≡ normSq z → r ≡ modulusℂ z
  modulusℂ-unique z = nonnegativeSqrtℝ-unique (normSq z) (normSq-nonnegative z)

  modulusℂ-zero : modulusℂ 0ℂ ≡ 0ℝ
  modulusℂ-zero = sqrt-cong _ _ normSq-zero ∙ nonnegativeSqrtℝ-zero (≤ℝ-refl 0ℝ)

  modulusℂ-one : modulusℂ 1ℂ ≡ 1ℝ
  modulusℂ-one = sqrt-cong _ _ normSq-one
    ∙ nonnegativeSqrtℝ-one (isNonnegative→0≤ 1ℝ oneIsNonnegative)

  modulusℂ-neg : ∀ z → modulusℂ (-ℂ z) ≡ modulusℂ z
  modulusℂ-neg z = sqrt-cong _ _ (normSq-neg z)

  modulusℂ-conjugate : ∀ z → modulusℂ (conjugate z) ≡ modulusℂ z
  modulusℂ-conjugate z = sqrt-cong _ _ (normSq-conjugate z)

  modulusℂ-fromℝ : ∀ x → modulusℂ (fromℝ x) ≡ absℝ x
  modulusℂ-fromℝ x = sqrt-cong _ _
    (cong (x · x +_) (ℝRing.0RightAnnihilates 0ℝ) ∙ addIdR (x · x))
    ∙ nonnegativeSqrtℝ-squareOf x (isNonnegative→0≤ (x · x) (squareIsNonnegative x))

  modulusℂ-mul : ∀ z w → modulusℂ (z ·ℂ w) ≡ modulusℂ z · modulusℂ w
  modulusℂ-mul z w = sqrt-cong _ _ (normSq-mul z w)
    ∙ nonnegativeSqrtℝ-mul (normSq z) (normSq w)
      (normSq-nonnegative z) (normSq-nonnegative w)
      (subst (0ℝ ≤ℝ_) (normSq-mul z w) (normSq-nonnegative (z ·ℂ w)))
