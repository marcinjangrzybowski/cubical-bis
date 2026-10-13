module Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_]; fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink

-- For N = suc n nonconstant coefficients, N * 4^(-N) ≤ 1/4.
-- This allows a uniform bound per remaining term instead of two geometric sums.
degreeShrink : ℕ → ℝ
degreeShrink n = powℝ descentShrink (suc n)

degreeShrink-positive : ∀ n → 0ℝ <ℝ degreeShrink n
degreeShrink-positive n = powPositive descentShrink (suc n) descentShrink-positive

degreeShrink≤quarter : ∀ n → degreeShrink n ≤ℝ descentShrink
degreeShrink≤quarter n = powPositiveExponent≤Base descentShrink n
  (<ℝ-weaken 0ℝ descentShrink descentShrink-positive) descentShrink≤one

degreeShrink<one : ∀ n → degreeShrink n <ℝ 1ℝ
degreeShrink<one n = ≤<ℝ-trans (degreeShrink n) descentShrink 1ℝ (degreeShrink≤quarter n) descentShrink<one

degreeShrink≤one : ∀ n → degreeShrink n ≤ℝ 1ℝ
degreeShrink≤one n = <ℝ-weaken (degreeShrink n) 1ℝ (degreeShrink<one n)

degreeShrink-error : ∀ n ε → degreeShrink n · rat (fst ε) ≤ℝ rat (fst (ε /2₊))
degreeShrink-error n ε = ≤ℝ-trans (degreeShrink n · rat (fst ε)) (descentShrink · rat (fst ε))
  (rat (fst (ε /2₊)))
  (mulPres≤R-0≤ (degreeShrink n) descentShrink (rat (fst ε))
    (<ℝ-weaken 0ℝ (rat (fst ε)) (<ℚ→<ℝ 0 (fst ε) (snd ε))) (degreeShrink≤quarter n))
  (descentShrink-error ε)

private
  quarter : ℚ
  quarter = [ pos 1 / 1+ 3 ]

  quarterStep : descentShrink · (descentShrink + descentShrink) ≤ℝ descentShrink
  quarterStep = <ℝ-weaken (descentShrink · (descentShrink + descentShrink)) descentShrink
    (subst (_<ℝ descentShrink)
      (sym (cong (descentShrink ·_) (rat+rat quarter quarter) ∙ mul-rat quarter (quarter ℚ.+ quarter)))
      (<ℚ→<ℝ (quarter ℚ.· (quarter ℚ.+ quarter)) quarter (ℚ.pos<pos tt)))

  countStep : ∀ n q t → realNatural (suc n) · (q · t) ≡ q · (realNatural n · t + t)
  countStep n q t = cong (_· (q · t)) (realNatural-suc n)
    ∙ mulAssoc (realNatural n + 1ℝ) q t ∙ cong (_· t) (mulComm (realNatural n + 1ℝ) q)
    ∙ sym (mulAssoc q (realNatural n + 1ℝ) t)
    ∙ cong (q ·_) (mulDistL (realNatural n) 1ℝ t ∙ cong (realNatural n · t +_) (mulIdL t))

degreeShrink-countBound : ∀ n → realNatural (suc n) · degreeShrink n ≤ℝ descentShrink
degreeShrink-countBound zero = subst (_≤ℝ descentShrink)
  (sym (mulIdL (degreeShrink zero) ∙ mulIdR descentShrink)) (≤ℝ-refl descentShrink)
degreeShrink-countBound (suc n) = subst (_≤ℝ descentShrink) (sym (countStep (suc n) descentShrink (degreeShrink n)))
  (≤ℝ-trans (descentShrink · (realNatural (suc n) · degreeShrink n + degreeShrink n))
    (descentShrink · (descentShrink + descentShrink)) descentShrink
    (mulPres≤L (realNatural (suc n) · degreeShrink n + degreeShrink n) (descentShrink + descentShrink) descentShrink
      (0≤→isNonnegative descentShrink (<ℝ-weaken 0ℝ descentShrink descentShrink-positive))
      (addPres≤ (realNatural (suc n) · degreeShrink n) descentShrink (degreeShrink n) descentShrink
        (degreeShrink-countBound n) (degreeShrink≤quarter n))) quarterStep)
