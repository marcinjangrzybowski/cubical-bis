module Cubical.Analysis.Real.Algebra.Polynomial.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List; []; _∷_; map)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication


-- The coefficient list is in increasing degree order, just as it is for
-- `evaluatePolynomial`.  Replacing every coefficient by its absolute value
-- gives a nonnegative polynomial that controls evaluation on a closed ball.

polynomialMajorant : List ℝ → ℝ → ℝ
polynomialMajorant coefficients radius =
  evaluatePolynomial (map absℝ coefficients) radius


private
  addNonnegative : ∀ x y →
    0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
    0ℝ ≤ℝ x + y
  addNonnegative x y 0≤x 0≤y =
    subst (_≤ℝ (x + y))
      (addIdL 0ℝ)
      (≤ℝ-trans
        (0ℝ + 0ℝ) (x + 0ℝ) (x + y)
        (addPres≤R 0ℝ x 0ℝ 0≤x)
        (addPres≤L 0ℝ y x 0≤y))

  mulNonnegative : ∀ x y →
    0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
    0ℝ ≤ℝ x · y
  mulNonnegative x y 0≤x 0≤y =
    isNonnegative→0≤ (x · y)
      (mulPresIsNonnegative x y
        (0≤→isNonnegative x 0≤x)
        (0≤→isNonnegative y 0≤y))

polynomialMajorantNonnegative : ∀ coefficients radius →
  0ℝ ≤ℝ radius →
  0ℝ ≤ℝ polynomialMajorant coefficients radius
polynomialMajorantNonnegative [] radius 0≤radius =
  ≤ℝ-refl 0ℝ
polynomialMajorantNonnegative
  (a ∷ coefficients) radius 0≤radius =
  addNonnegative
    (absℝ a)
    (radius · polynomialMajorant coefficients radius)
    (absNonnegative a)
    (mulNonnegative
      radius (polynomialMajorant coefficients radius)
      0≤radius
      (polynomialMajorantNonnegative
        coefficients radius 0≤radius))


evaluatePolynomialAbsBound : ∀ coefficients x →
  absℝ (evaluatePolynomial coefficients x) ≤ℝ
  polynomialMajorant coefficients (absℝ x)
evaluatePolynomialAbsBound [] x =
  subst (_≤ℝ 0ℝ) (sym absZero) (≤ℝ-refl 0ℝ)
evaluatePolynomialAbsBound (a ∷ coefficients) x =
  ≤ℝ-trans
    (absℝ (a + x · evaluatePolynomial coefficients x))
    (absℝ a + absℝ (x · evaluatePolynomial coefficients x))
    (absℝ a
      + absℝ x · polynomialMajorant coefficients (absℝ x))
    (absTriangle a (x · evaluatePolynomial coefficients x))
    (subst
      (λ productAbs →
        absℝ a + productAbs ≤ℝ
        absℝ a
          + absℝ x · polynomialMajorant coefficients (absℝ x))
      (sym (absMul x (evaluatePolynomial coefficients x)))
      (addPres≤
        (absℝ a) (absℝ a)
        (absℝ x · absℝ (evaluatePolynomial coefficients x))
        (absℝ x · polynomialMajorant coefficients (absℝ x))
        (≤ℝ-refl (absℝ a))
        (mulPres≤L
          (absℝ (evaluatePolynomial coefficients x))
          (polynomialMajorant coefficients (absℝ x))
          (absℝ x)
          (0≤→isNonnegative (absℝ x) (absNonnegative x))
          (evaluatePolynomialAbsBound coefficients x))))


polynomialMajorantMono : ∀ coefficients x y →
  0ℝ ≤ℝ x →
  x ≤ℝ y →
  polynomialMajorant coefficients x ≤ℝ
  polynomialMajorant coefficients y
polynomialMajorantMono [] x y 0≤x x≤y =
  ≤ℝ-refl 0ℝ
polynomialMajorantMono
  (a ∷ coefficients) x y 0≤x x≤y =
  addPres≤
    (absℝ a) (absℝ a)
    (x · polynomialMajorant coefficients x)
    (y · polynomialMajorant coefficients y)
    (≤ℝ-refl (absℝ a))
    (mulPres≤
      x y
      (polynomialMajorant coefficients x)
      (polynomialMajorant coefficients y)
      (≤ℝ-trans 0ℝ x y 0≤x x≤y)
      (polynomialMajorantNonnegative coefficients x 0≤x)
      x≤y
      (polynomialMajorantMono coefficients x y 0≤x x≤y))
