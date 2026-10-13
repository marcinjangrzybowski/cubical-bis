module Cubical.Analysis.Complex.Polynomial.Quadratic.Disk where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Vec as Vec
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.RootCertificate
import Cubical.Analysis.Complex.Polynomial.Quadratic.Algebra as QuadraticDefinition

private
  module R = QuadraticDefinition.Quadratic ℝCommRing
  module C = QuadraticDefinition.Quadratic ℂCommRing

quadraticPolynomial : ℂ → MonicPolynomial 2
quadraticPolynomial c = c Vec.∷ (-ℂ 1ℂ) Vec.∷ Vec.[]

private
  coefficients : ℂ → List ℂ
  coefficients c = c ∷ 0ℂ ∷ 1ℂ ∷ []

  opaque
    bound-formula : ∀ c radius →
      polynomialBoundℂ (coefficients c) radius ≡ normℂ c + radius · radius
    bound-formula c radius =
      cong₂ (λ zeroNorm oneNorm → normℂ c + radius · (zeroNorm + radius · (oneNorm + radius · 0ℝ)))
        normℂ-zero normℂ-one
      ∙ R.boundFormula (normℂ c) radius

    lipschitz-formula : ∀ c radius →
      polynomialLipschitzBoundℂ (coefficients c) radius ≡ radius + radius
    lipschitz-formula c radius =
      cong₂ (λ zeroNorm oneNorm →
        (zeroNorm + radius · (oneNorm + radius · 0ℝ)) +
        radius · ((oneNorm + radius · 0ℝ) + radius · (0ℝ + radius · 0ℝ)))
        normℂ-zero normℂ-one
      ∙ R.lipschitzFormula radius

    evaluate-formula : ∀ c z → evaluatePolynomialℂ (coefficients c) z ≡ c +ℂ z ·ℂ z
    evaluate-formula c z = evaluatePolynomialℂ-quadratic c 0ℂ 1ℂ z
      ∙ cong (λ t → c +ℂ z ·ℂ t)
        (+ℂComm 0ℂ (z ·ℂ 1ℂ) ∙ +ℂIdR (z ·ℂ 1ℂ) ∙ ·ℂIdR z)

-- A local square-root branch expressed as z²-z+c=0. The two elementary
-- inequalities on the disk replace any global choice of a square root.
module QuadraticDisk (c : ℂ) (radius : ℝ)
  (radius-nonnegative : 0ℝ ≤ℝ radius)
  (small-radius : radius + radius <ℝ 1ℝ)
  (small-constant : normℂ c + radius · radius ≤ℝ radius) where

  private
    twice-nonnegative : 0ℝ ≤ℝ radius + radius
    twice-nonnegative = subst (_≤ℝ radius + radius) (addIdL 0ℝ)
      (addPres≤ 0ℝ radius 0ℝ radius radius-nonnegative radius-nonnegative)

    bound : polynomialBoundℂ (coefficients c) radius ≤ℝ radius
    bound = subst (_≤ℝ radius) (sym (bound-formula c radius)) small-constant

    lip : polynomialLipschitzBoundℂ (coefficients c) radius ≤ℝ radius + radius
    lip = subst (_≤ℝ radius + radius) (sym (lipschitz-formula c radius))
      (≤ℝ-refl (radius + radius))

    module P = PolynomialFixedPoint (coefficients c) radius (radius + radius)
      radius-nonnegative twice-nonnegative small-radius bound lip

  opaque
    quadraticRoot : ℂ
    quadraticRoot = fst P.polynomialFixedPoint

    quadraticRoot-bound : normℂ quadraticRoot ≤ℝ radius
    quadraticRoot-bound = fst (snd P.polynomialFixedPoint)

    quadraticRoot-fixed : c +ℂ quadraticRoot ·ℂ quadraticRoot ≡ quadraticRoot
    quadraticRoot-fixed = sym (evaluate-formula c quadraticRoot) ∙ snd (snd P.polynomialFixedPoint)

    quadraticRoot-equation : evaluateMonic (quadraticPolynomial c) quadraticRoot ≡ 0ℂ
    quadraticRoot-equation = C.fixedToRoot c quadraticRoot quadraticRoot-fixed

    quadraticRoot-unique : ∀ z → normℂ z ≤ℝ radius →
      evaluateMonic (quadraticPolynomial c) z ≡ 0ℂ → z ≡ quadraticRoot
    quadraticRoot-unique z zb root = P.polynomialFixedPoint-unique z zb
      (evaluate-formula c z ∙ C.rootToFixed c z root)
