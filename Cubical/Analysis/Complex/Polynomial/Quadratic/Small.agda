module Cubical.Analysis.Complex.Polynomial.Quadratic.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Quadratic.Disk

private
  quarter eighth : ℚ
  quarter = [ pos 1 / 1+ 3 ]
  eighth = [ pos 1 / 1+ 7 ]

quadraticBranchRadius quadraticConstantBound : ℝ
quadraticBranchRadius = rat quarter
quadraticConstantBound = rat eighth

private
  radius-nonnegative : 0ℝ ≤ℝ quadraticBranchRadius
  radius-nonnegative = <ℝ-weaken 0ℝ quadraticBranchRadius
    (<ℚ→<ℝ 0 quarter (ℚ.pos<pos tt))

  small-radius : quadraticBranchRadius + quadraticBranchRadius <ℝ 1ℝ
  small-radius = subst (_<ℝ 1ℝ) (sym (rat+rat quarter quarter))
    (<ℚ→<ℝ (quarter ℚ.+ quarter) 1 (ℚ.pos<pos tt))

  allowance : quadraticConstantBound + quadraticBranchRadius · quadraticBranchRadius ≤ℝ quadraticBranchRadius
  allowance = subst (_≤ℝ quadraticBranchRadius)
    (sym (cong (quadraticConstantBound +_) (mul-rat quarter quarter)
      ∙ rat+rat eighth (quarter ℚ.· quarter)))
    (invEq (rat≤rat≃ (eighth ℚ.+ quarter ℚ.· quarter) quarter)
      (ℚ.<Weaken≤ _ _ (ℚ.pos<pos tt)))

module _ (c : ℂ) (small : normℂ c ≤ℝ quadraticConstantBound) where
  private
    small-constant : normℂ c + quadraticBranchRadius · quadraticBranchRadius ≤ℝ quadraticBranchRadius
    small-constant = ≤ℝ-trans
      (normℂ c + quadraticBranchRadius · quadraticBranchRadius)
      (quadraticConstantBound + quadraticBranchRadius · quadraticBranchRadius) quadraticBranchRadius
      (addPres≤R (normℂ c) quadraticConstantBound
        (quadraticBranchRadius · quadraticBranchRadius) small) allowance

    module D = QuadraticDisk c quadraticBranchRadius radius-nonnegative small-radius small-constant

  opaque
    smallQuadraticRoot : ℂ
    smallQuadraticRoot = D.quadraticRoot

    smallQuadraticRoot-bound : normℂ smallQuadraticRoot ≤ℝ quadraticBranchRadius
    smallQuadraticRoot-bound = D.quadraticRoot-bound

    smallQuadraticRoot-equation : evaluateMonic (quadraticPolynomial c) smallQuadraticRoot ≡ 0ℂ
    smallQuadraticRoot-equation = D.quadraticRoot-equation

    smallQuadraticRoot-unique : ∀ z → normℂ z ≤ℝ quadraticBranchRadius →
      evaluateMonic (quadraticPolynomial c) z ≡ 0ℂ → z ≡ smallQuadraticRoot
    smallQuadraticRoot-unique = D.quadraticRoot-unique
