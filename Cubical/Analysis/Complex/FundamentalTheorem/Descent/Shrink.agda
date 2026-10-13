module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink where

open import Cubical.Foundations.Prelude
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
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational

private
  quarter half : ℚ
  quarter = [ pos 1 / 1+ 3 ]
  half = [ pos 1 / 1+ 1 ]

descentShrink : ℝ
descentShrink = rat quarter

descentShrink-positive : 0ℝ <ℝ descentShrink
descentShrink-positive = <ℚ→<ℝ 0 quarter (ℚ.pos<pos tt)

descentShrink<one : descentShrink <ℝ 1ℝ
descentShrink<one = <ℚ→<ℝ quarter 1 (ℚ.pos<pos tt)

descentShrink≤one : descentShrink ≤ℝ 1ℝ
descentShrink≤one = <ℝ-weaken descentShrink 1ℝ descentShrink<one

descentShrink-error : ∀ ε → descentShrink · rat (fst ε) ≤ℝ rat (fst (ε /2₊))
descentShrink-error ε = <ℝ-weaken (descentShrink · rat (fst ε)) (rat (fst (ε /2₊)))
  (subst (descentShrink · rat (fst ε) <ℝ_)
    (mul-rat half (fst ε) ∙ cong rat (ℚ.·Comm half (fst ε)))
    (mulPres<PosR descentShrink (rat half) (rat (fst ε))
      (<ℚ→<ℝ 0 (fst ε) (snd ε)) (<ℚ→<ℝ quarter half (ℚ.pos<pos tt))))
