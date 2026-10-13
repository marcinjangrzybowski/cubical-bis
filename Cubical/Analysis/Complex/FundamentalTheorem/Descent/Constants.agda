module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_]; fromNatℚ; eq/)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink

private
  half quarter eighth : ℚ
  half = [ pos 1 / 1+ 1 ]
  quarter = [ pos 1 / 1+ 3 ]
  eighth = [ pos 1 / 1+ 7 ]

descentHalf descentEighth : ℝ
descentHalf = rat half
descentEighth = rat eighth

descentHalf-positive : 0ℝ <ℝ descentHalf
descentHalf-positive = <ℚ→<ℝ 0 half (ℚ.pos<pos tt)

descentEighth-positive : 0ℝ <ℝ descentEighth
descentEighth-positive = <ℚ→<ℝ 0 eighth (ℚ.pos<pos tt)

descentEighth<one : descentEighth <ℝ 1ℝ
descentEighth<one = <ℚ→<ℝ eighth 1 (ℚ.pos<pos tt)

opaque
  descentHalf-double : descentHalf + descentHalf ≡ 1ℝ
  descentHalf-double = rat+rat half half ∙ cong rat (eq/ _ _ refl)

  descentQuarter-double : descentShrink + descentShrink ≡ descentHalf
  descentQuarter-double = rat+rat quarter quarter ∙ cong rat (eq/ _ _ refl)

  descentHalf-square : descentHalf · descentHalf ≡ descentShrink
  descentHalf-square = mul-rat half half ∙ cong rat (eq/ _ _ refl)

  descentQuarter-half : descentShrink · descentHalf ≡ descentEighth
  descentQuarter-half = mul-rat quarter half ∙ cong rat (eq/ _ _ refl)

  halfScaleDouble : ∀ x → descentHalf · x + descentHalf · x ≡ x
  halfScaleDouble x = sym (mulDistL descentHalf descentHalf x)
    ∙ cong (_· x) descentHalf-double ∙ mulIdL x

  quarterScaleDouble : ∀ x → descentShrink · x + descentShrink · x ≡ descentHalf · x
  quarterScaleDouble x = sym (mulDistL descentShrink descentShrink x) ∙ cong (_· x) descentQuarter-double

  halfScaleHalf : ∀ x → descentHalf · (descentHalf · x) ≡ descentShrink · x
  halfScaleHalf x = mulAssoc descentHalf descentHalf x ∙ cong (_· x) descentHalf-square

  quarterScaleHalf : ∀ x → descentShrink · (descentHalf · x) ≡ descentEighth · x
  quarterScaleHalf x = mulAssoc descentShrink descentHalf x ∙ cong (_· x) descentQuarter-half

  subtractDoubleCancel : ∀ x y → (x - (y + y)) + y ≡ x - y
  subtractDoubleCancel x y = cong (λ z → (x + z) + y) (negAdd y y)
    ∙ sym (addAssoc x ((- y) + (- y)) y)
    ∙ cong (x +_) (sym (addAssoc (- y) (- y) y)
      ∙ cong ((- y) +_) (addInvL y) ∙ addIdR (- y))

  subtractHalfCancel : ∀ x y → (x - y) + descentHalf · y ≡ x - descentHalf · y
  subtractHalfCancel x y = cong (λ z → (x - z) + descentHalf · y) (sym (halfScaleDouble y))
    ∙ subtractDoubleCancel x (descentHalf · y)

  oneMinusTwice : ∀ x → 1ℝ - (1ℝ - x) ≡ x
  oneMinusTwice x = cong (1ℝ +_) (negAdd 1ℝ (- x) ∙ cong ((- 1ℝ) +_) (negInvol x))
    ∙ addAssoc 1ℝ (- 1ℝ) x ∙ cong (_+ x) (addInvR 1ℝ) ∙ addIdL x
