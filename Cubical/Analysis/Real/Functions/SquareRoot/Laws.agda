module Cubical.Analysis.Real.Functions.SquareRoot.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Tactics.CommRingSolver

private
  module Algebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)

    productSquare : ∀ x y → (x · y) · (x · y) ≡ (x · x) · (y · y)
    productSquare x y = solve! R

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Functions.SquareRoot.Positive
open import Cubical.Analysis.Real.Functions.SquareRoot.Nonnegative

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

nonnegativeSqrtℝ-independent : ∀ x p q → nonnegativeSqrtℝ x p ≡ nonnegativeSqrtℝ x q
nonnegativeSqrtℝ-independent x p q = cong (nonnegativeSqrtℝ x) (isProp≤ℝ 0ℝ x p q)

nonnegativeSqrtℝ-zero : ∀ p → nonnegativeSqrtℝ 0ℝ p ≡ 0ℝ
nonnegativeSqrtℝ-zero p = sym
  (nonnegativeSqrtℝ-unique 0ℝ p 0ℝ (≤ℝ-refl 0ℝ) (ℝRing.0RightAnnihilates 0ℝ))

nonnegativeSqrtℝ-one : ∀ p → nonnegativeSqrtℝ 1ℝ p ≡ 1ℝ
nonnegativeSqrtℝ-one p = sym
  (nonnegativeSqrtℝ-unique 1ℝ p 1ℝ (isNonnegative→0≤ 1ℝ oneIsNonnegative) (mulIdR 1ℝ))

nonnegativeSqrtℝ-squareOf : ∀ x p → nonnegativeSqrtℝ (x · x) p ≡ absℝ x
nonnegativeSqrtℝ-squareOf x p = sym
  (nonnegativeSqrtℝ-unique (x · x) p (absℝ x) (absNonnegative x) (absSquared x))

nonnegativeSqrtℝ-positiveAgreement : ∀ x p positive →
  nonnegativeSqrtℝ x p ≡ positiveSqrtℝ x positive
nonnegativeSqrtℝ-positiveAgreement x p positive = positiveSqrtℝ-unique x positive
  (nonnegativeSqrtℝ x p) (nonnegativeSqrtℝ-nonnegative x p) (nonnegativeSqrtℝ-square x p)

nonnegativeSqrtℝ-monotone : ∀ x y xp yp → x ≤ℝ y →
  nonnegativeSqrtℝ x xp ≤ℝ nonnegativeSqrtℝ y yp
nonnegativeSqrtℝ-monotone x y xp yp ordered = squareReflects≤Nonnegative
  (nonnegativeSqrtℝ x xp) (nonnegativeSqrtℝ y yp) (nonnegativeSqrtℝ-nonnegative y yp)
  (subst2 _≤ℝ_ (sym (nonnegativeSqrtℝ-square x xp)) (sym (nonnegativeSqrtℝ-square y yp)) ordered)

nonnegativeSqrtℝ-mul : ∀ x y xp yp product-nonnegative →
  nonnegativeSqrtℝ (x · y) product-nonnegative ≡ nonnegativeSqrtℝ x xp · nonnegativeSqrtℝ y yp
nonnegativeSqrtℝ-mul x y xp yp product-nonnegative = sym
  (nonnegativeSqrtℝ-unique (x · y) product-nonnegative
    (nonnegativeSqrtℝ x xp · nonnegativeSqrtℝ y yp)
    (isNonnegative→0≤ _ (mulPresIsNonnegative _ _
      (0≤→isNonnegative _ (nonnegativeSqrtℝ-nonnegative x xp))
      (0≤→isNonnegative _ (nonnegativeSqrtℝ-nonnegative y yp))))
    (Algebra.productSquare ℝCommRing (nonnegativeSqrtℝ x xp) (nonnegativeSqrtℝ y yp)
      ∙ cong₂ _·_ (nonnegativeSqrtℝ-square x xp) (nonnegativeSqrtℝ-square y yp)))
