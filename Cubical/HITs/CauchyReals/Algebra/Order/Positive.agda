module Cubical.HITs.CauchyReals.Algebra.Order.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance


positiveAddClosed : ∀ x y → 0 <ᵣ x → 0 <ᵣ y → 0 <ᵣ x +ᵣ y
positiveAddClosed x y 0<x 0<y = ℝ₊+ (x , 0<x) (y , 0<y)

positiveMulClosed : ∀ x y → 0 <ᵣ x → 0 <ᵣ y → 0 <ᵣ x ·ᵣ y
positiveMulClosed x y 0<x 0<y = ℝ₊· (x , 0<x) (y , 0<y)

module PositiveReals =
  Positive ℝOrderedCommRing positiveAddClosed positiveMulClosed


nonNegativeAddClosed : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x +ᵣ y
nonNegativeAddClosed x y 0≤x 0≤y =
  isTrans≤ᵣ 0 x (x +ᵣ y) 0≤x
    (ℝOrder.≤SumLeftNonNeg x y 0≤y)
  where
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing

nonNegativeMulClosed : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x ·ᵣ y
nonNegativeMulClosed x y 0≤x 0≤y =
  isTrans≡≤ᵣ 0 (0 ·ᵣ y) (x ·ᵣ y)
    (sym (Rℝ.0LeftAnnihilates y))
    (≤ᵣ-·ᵣo 0 x y 0≤y 0≤x)

module NonNegativeReals =
  NonNegative ℝOrderedCommRing nonNegativeAddClosed nonNegativeMulClosed


ℝ₊≡PositiveReals : ℝ₊ ≡ PositiveReals.R₊
ℝ₊≡PositiveReals = refl

ℝ₀₊≡NonNegativeReals : ℝ₀₊ ≡ NonNegativeReals.R₀₊
ℝ₀₊≡NonNegativeReals = refl
