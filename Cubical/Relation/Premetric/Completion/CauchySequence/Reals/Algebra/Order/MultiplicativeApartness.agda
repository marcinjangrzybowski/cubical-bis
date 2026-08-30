module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.OrderedCommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  negativeNegationPositive : ∀ {x} →
    x <ℝ Real.ιℚ 0 → Real.ιℚ 0 <ℝ (Neg.- x)
  negativeNegationPositive {x} x<0 =
    subst2 _<ℝ_ neg-zero refl
      (<ℝ-neg x (Real.ιℚ 0) x<0)

  positiveNegationNegative : ∀ {x} →
    Real.ιℚ 0 <ℝ (Neg.- x) → x <ℝ Real.ιℚ 0
  positiveNegationNegative {x} 0<-x =
    subst2 _<ℝ_ (Neg.neg-involutive x) neg-zero
      (<ℝ-neg (Real.ιℚ 0) (Neg.- x) 0<-x)


-- Apartness is multiplicative.  The four sign cases retain enough positive
-- information to construct a strict gap for the product; no decidable
-- equality or excluded middle is used.

apartMul : ∀ x y →
  Real.ιℚ 0 ＃ x →
  Real.ιℚ 0 ＃ y →
  Real.ιℚ 0 ＃ (x Mul.· y)
apartMul x y (inl 0<x) (inl 0<y) =
  inl (mul-positive x y 0<x 0<y)
apartMul x y (inl 0<x) (inr y<0) =
  inr
    (positiveNegationNegative
      (subst
        (Real.ιℚ 0 <ℝ_)
        (ℝRing.-DistR· x y)
        (mul-positive x (Neg.- y)
          0<x (negativeNegationPositive y<0))))
apartMul x y (inr x<0) (inl 0<y) =
  inr
    (positiveNegationNegative
      (subst
        (Real.ιℚ 0 <ℝ_)
        (ℝRing.-DistL· x y)
        (mul-positive (Neg.- x) y
          (negativeNegationPositive x<0) 0<y)))
apartMul x y (inr x<0) (inr y<0) =
  inl
    (subst
      (Real.ιℚ 0 <ℝ_)
      (ℝRing.-Dist· x y)
      (mul-positive (Neg.- x) (Neg.- y)
        (negativeNegationPositive x<0)
        (negativeNegationPositive y<0)))


apartOne : Real.ιℚ 0 ＃ Real.ιℚ 1
apartOne =
  inl (isOrderedCommRingℝ .IsOrderedCommRing.0<1)


apartPow : ∀ x n →
  Real.ιℚ 0 ＃ x →
  Real.ιℚ 0 ＃ (x ^ⁿ n)
apartPow x zero x-apart =
  apartOne
apartPow x (suc n) x-apart =
  apartMul x (x ^ⁿ n) x-apart (apartPow x n x-apart)
