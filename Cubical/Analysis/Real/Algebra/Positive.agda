module Cubical.Analysis.Real.Algebra.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base using (ℝ; rat; isSetℝ)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addIdR)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
  using (<ℚ→<ℝ; rat<rat≃)
open import Cubical.Analysis.Real.Order.Strict.Addition using (<ℝ-add)
open import Cubical.Analysis.Real.Order.Strict.Multiplication
  using (mulPositive)

open ℚInstance.PositiveRationals using (ℚ₊)


IsPositive : ℝ → Type₀
IsPositive x = 0ℝ <ℝ x

isPropIsPositive : ∀ x → isProp (IsPositive x)
isPropIsPositive x = isProp<ℝ 0ℝ x

ratIsPositive≃ : ∀ q → IsPositive (rat q) ≃ (0 ℚOrder.< q)
ratIsPositive≃ q = rat<rat≃ 0 q

ℝ>0 : Type₀
ℝ>0 = Σ[ x ∈ ℝ ] IsPositive x

isSetℝ>0 : isSet ℝ>0
isSetℝ>0 = isSetΣSndProp isSetℝ isPropIsPositive

positiveRat : ℚ₊ → ℝ>0
positiveRat δ =
  rat (fst δ) , <ℚ→<ℝ 0 (fst δ) (snd δ)

infixl 6 _+>0_
infixl 7 _·>0_

_+>0_ : ℝ>0 → ℝ>0 → ℝ>0
(x , 0<x) +>0 (y , 0<y) =
  x + y ,
  subst (λ z → z <ℝ x + y) (addIdR 0ℝ)
    (<ℝ-add 0ℝ x 0ℝ y 0<x 0<y)

_·>0_ : ℝ>0 → ℝ>0 → ℝ>0
(x , 0<x) ·>0 (y , 0<y) =
  x · y , mulPositive x y 0<x 0<y
