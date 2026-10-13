module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Factor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SelectedTerm

descentSelectedFactor : ℕ → ℝ
descentSelectedFactor n = selectedTermFactor n (degreeShrink n)

descentSelectedFactor-positive : ∀ n → 0ℝ <ℝ descentSelectedFactor n
descentSelectedFactor-positive n = selectedTermFactor-positive n (degreeShrink n) (degreeShrink-positive n)

descentSelectedFactor<one : ∀ n → descentSelectedFactor n <ℝ 1ℝ
descentSelectedFactor<one n = selectedTermFactor<one n (degreeShrink n) (degreeShrink-positive n) (degreeShrink<one n)

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

  opaque
    lossScale : ∀ φ A → A - descentShrink · (φ · (descentHalf · A)) ≡ (1ℝ - descentEighth · φ) · A
    lossScale φ A = cong (A -_)
      (cong (descentShrink ·_) (mulAssoc φ descentHalf A
        ∙ cong (_· A) (mulComm φ descentHalf) ∙ sym (mulAssoc descentHalf φ A))
        ∙ quarterScaleHalf (φ · A) ∙ mulAssoc descentEighth φ A)
      ∙ sym (R.·DistL- 1ℝ (descentEighth · φ) A ∙ cong (_- ((descentEighth · φ) · A)) (mulIdL A))

opaque
  -- This factor is independent of coefficients and of requested accuracy.
  descentContraction : ℕ → ℝ
  descentContraction n = 1ℝ - descentEighth · descentSelectedFactor n

  descentContraction-positive : ∀ n → 0ℝ <ℝ descentContraction n
  descentContraction-positive n = positiveSub (descentEighth · descentSelectedFactor n) 1ℝ
    (<ℝ-trans (descentEighth · descentSelectedFactor n) descentEighth 1ℝ
      (subst (descentEighth · descentSelectedFactor n <ℝ_) (mulIdR descentEighth)
        (mulPres<PosL (descentSelectedFactor n) 1ℝ descentEighth descentEighth-positive (descentSelectedFactor<one n)))
      descentEighth<one)

  descentContraction<one : ∀ n → descentContraction n <ℝ 1ℝ
  descentContraction<one n = positiveSub→< (descentContraction n) 1ℝ
    (subst (0ℝ <ℝ_) (sym (oneMinusTwice (descentEighth · descentSelectedFactor n)))
      (mulPositive descentEighth (descentSelectedFactor n) descentEighth-positive (descentSelectedFactor-positive n)))

  descentContraction-scale : ∀ n A →
    A - descentShrink · (descentSelectedFactor n · (descentHalf · A)) ≡ descentContraction n · A
  descentContraction-scale n A = lossScale (descentSelectedFactor n) A
