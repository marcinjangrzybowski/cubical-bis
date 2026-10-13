module Cubical.Analysis.Complex.Polynomial.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds.Step
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

private
  module C = IdentitiesDefinition.Identities ℂCommRing
  module R = RingTheory (CommRing→Ring ℝCommRing)

polynomialBoundℂ : List ℂ → ℝ → ℝ
polynomialBoundℂ [] radius = 0ℝ
polynomialBoundℂ (a ∷ p) radius = normℂ a + radius · polynomialBoundℂ p radius

polynomialLipschitzBoundℂ : List ℂ → ℝ → ℝ
polynomialLipschitzBoundℂ [] radius = 0ℝ
polynomialLipschitzBoundℂ (a ∷ p) radius =
  polynomialBoundℂ p radius + radius · polynomialLipschitzBoundℂ p radius

opaque
  evaluatePolynomialℂ-bound : ∀ p radius z → normℂ z ≤ℝ radius →
    normℂ (evaluatePolynomialℂ p z) ≤ℝ polynomialBoundℂ p radius
  evaluatePolynomialℂ-bound [] radius z bounded = subst (_≤ℝ 0ℝ)
    (sym (cong normℂ (evaluatePolynomialℂ-empty z) ∙ normℂ-zero)) (≤ℝ-refl 0ℝ)
  evaluatePolynomialℂ-bound (a ∷ p) radius z bounded =
    subst (_≤ℝ polynomialBoundℂ (a ∷ p) radius)
      (sym (cong normℂ (evaluatePolynomialℂ-cons a p z)))
      (hornerBoundℂ a z (evaluatePolynomialℂ p z) radius (polynomialBoundℂ p radius)
        bounded (evaluatePolynomialℂ-bound p radius z bounded))

  evaluatePolynomialℂ-lipschitz : ∀ p radius z w →
    normℂ z ≤ℝ radius → normℂ w ≤ℝ radius →
    normℂ (evaluatePolynomialℂ p z -ℂ evaluatePolynomialℂ p w) ≤ℝ
      polynomialLipschitzBoundℂ p radius · normℂ (z -ℂ w)
  evaluatePolynomialℂ-lipschitz [] radius z w zb wb = subst2 _≤ℝ_
    (sym (cong normℂ
      (cong₂ _-ℂ_ (evaluatePolynomialℂ-empty z) (evaluatePolynomialℂ-empty w)
        ∙ +ℂInvR 0ℂ) ∙ normℂ-zero))
    (sym (R.0LeftAnnihilates (normℂ (z -ℂ w)))) (≤ℝ-refl 0ℝ)
  evaluatePolynomialℂ-lipschitz (a ∷ p) radius z w zb wb =
    subst (_≤ℝ polynomialLipschitzBoundℂ (a ∷ p) radius · normℂ (z -ℂ w))
      (sym (cong normℂ (cong₂ _-ℂ_
        (evaluatePolynomialℂ-cons a p z) (evaluatePolynomialℂ-cons a p w))))
      (hornerLipschitzℂ a z w (evaluatePolynomialℂ p z) (evaluatePolynomialℂ p w)
        radius (polynomialBoundℂ p radius) (polynomialLipschitzBoundℂ p radius)
        wb (evaluatePolynomialℂ-bound p radius z zb)
        (evaluatePolynomialℂ-lipschitz p radius z w zb wb))

  polynomialBound-nonnegativeℂ : ∀ p radius → 0ℝ ≤ℝ radius →
    0ℝ ≤ℝ polynomialBoundℂ p radius
  polynomialBound-nonnegativeℂ p radius nonnegative =
    ≤ℝ-trans 0ℝ (normℂ (evaluatePolynomialℂ p 0ℂ)) (polynomialBoundℂ p radius)
      (normℂ-nonnegative (evaluatePolynomialℂ p 0ℂ))
      (evaluatePolynomialℂ-bound p radius 0ℂ (subst (_≤ℝ radius) (sym normℂ-zero) nonnegative))
