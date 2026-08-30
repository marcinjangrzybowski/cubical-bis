module Cubical.Analysis.Real.Algebra.Nonnegative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue

open OrderedCommRingTheory ℚOrderedCommRing


IsNonnegative : ℝ → Type₀
IsNonnegative x = absℝ x ≡ x

isPropIsNonnegative : ∀ x → isProp (IsNonnegative x)
isPropIsNonnegative x = isSetℝ (absℝ x) x

ratIsNonnegative≃ : ∀ q →
  IsNonnegative (rat q) ≃ (0 ℚ.≤ q)
ratIsNonnegative≃ q = propBiimpl→Equiv
  (isPropIsNonnegative (rat q)) (ℚ.isProp≤ _ _)
  toRational fromRational
  where
  toRational : IsNonnegative (rat q) → 0 ℚ.≤ q
  toRational fixed = subst (0 ℚ.≤_)
    (rat-injective (sym (abs-rat q) ∙ fixed))
    (0≤abs q)

  fromRational : 0 ℚ.≤ q → IsNonnegative (rat q)
  fromRational 0≤q =
    abs-rat q ∙ cong rat (0≤→abs≡id q 0≤q)

zeroIsNonnegative : IsNonnegative 0ℝ
zeroIsNonnegative = absZero

oneIsNonnegative : IsNonnegative 1ℝ
oneIsNonnegative = absOne

absIsNonnegative : ∀ x → IsNonnegative (absℝ x)
absIsNonnegative = absIdem

addPresIsNonnegative : ∀ x y →
  IsNonnegative x → IsNonnegative y → IsNonnegative (x + y)
addPresIsNonnegative x y x≥0 y≥0 =
  cong absℝ (cong₂ _+_ (sym x≥0) (sym y≥0))
  ∙ absAddAbs x y
  ∙ cong₂ _+_ x≥0 y≥0

mulPresIsNonnegative : ∀ x y →
  IsNonnegative x → IsNonnegative y → IsNonnegative (x · y)
mulPresIsNonnegative x y x≥0 y≥0 =
  absMul x y ∙ cong₂ _·_ x≥0 y≥0

squareIsNonnegative : ∀ x → IsNonnegative (x · x)
squareIsNonnegative x = absMul x x ∙ absSquared x


-- The fixed points of absolute value form the nonnegative cone without a
-- prior definition of the full order on reals.

ℝ≥0 : Type₀
ℝ≥0 = Σ[ x ∈ ℝ ] IsNonnegative x

isSetℝ≥0 : isSet ℝ≥0
isSetℝ≥0 = isSetΣSndProp isSetℝ isPropIsNonnegative

infixl 6 _+≥0_
infixl 7 _·≥0_

0≥0 1≥0 : ℝ≥0
0≥0 = 0ℝ , zeroIsNonnegative
1≥0 = 1ℝ , oneIsNonnegative

_+≥0_ : ℝ≥0 → ℝ≥0 → ℝ≥0
(x , x≥0) +≥0 (y , y≥0) =
  x + y , addPresIsNonnegative x y x≥0 y≥0

_·≥0_ : ℝ≥0 → ℝ≥0 → ℝ≥0
(x , x≥0) ·≥0 (y , y≥0) =
  x · y , mulPresIsNonnegative x y x≥0 y≥0
