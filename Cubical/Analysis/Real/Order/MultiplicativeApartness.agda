module Cubical.Analysis.Real.Order.MultiplicativeApartness where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sum as ⊎

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Functions.Powers


private
  module ℝRing = RingProperties.RingTheory (CommRing→Ring ℝCommRing)


negativeNegationPositive : ∀ {x} →
  x <ℝ 0ℝ → 0ℝ <ℝ (- x)
negativeNegationPositive {x} x<0 =
  subst (_<ℝ (- x)) negZero
    (<ℝ-neg x 0ℝ x<0)


positiveNegationNegative : ∀ {x} →
  0ℝ <ℝ (- x) → x <ℝ 0ℝ
positiveNegationNegative {x} 0<-x =
  subst (_<ℝ 0ℝ) (negInvol x)
    (subst ((- (- x)) <ℝ_) negZero
      (<ℝ-neg 0ℝ (- x) 0<-x))


negationOfPositiveNegative : ∀ {x} →
  0ℝ <ℝ x → (- x) <ℝ 0ℝ
negationOfPositiveNegative {x} 0<x =
  subst ((- x) <ℝ_) negZero
    (<ℝ-neg 0ℝ x 0<x)


apartMul : ∀ x y →
  0ℝ #ℝ x →
  0ℝ #ℝ y →
  0ℝ #ℝ (x · y)
apartMul x y (inl 0<x) (inl 0<y) =
  inl (mulPositive x y 0<x 0<y)
apartMul x y (inl 0<x) (inr y<0) =
  inr
    (positiveNegationNegative {x = x · y}
      (subst
        (0ℝ <ℝ_)
        rightNegativePath
        (mulPositive x (- y)
          0<x (negativeNegationPositive {x = y} y<0))))
  where
  rightNegativePath : x · (- y) ≡ - (x · y)
  rightNegativePath = ℝRing.-DistR· x y
apartMul x y (inr x<0) (inl 0<y) =
  inr
    (positiveNegationNegative {x = x · y}
      (subst
        (0ℝ <ℝ_)
        leftNegativePath
        (mulPositive (- x) y
          (negativeNegationPositive {x = x} x<0) 0<y)))
  where
  leftNegativePath : (- x) · y ≡ - (x · y)
  leftNegativePath = ℝRing.-DistL· x y
apartMul x y (inr x<0) (inr y<0) =
  inl
    (subst
      (0ℝ <ℝ_)
      doubleNegativePath
      (mulPositive (- x) (- y)
        (negativeNegationPositive {x = x} x<0)
        (negativeNegationPositive {x = y} y<0)))
  where
  doubleNegativePath : (- x) · (- y) ≡ x · y
  doubleNegativePath = ℝRing.-Dist· x y


apartOne : 0ℝ #ℝ 1ℝ
apartOne = inl (isOrderedCommRingℝ .IsOrderedCommRing.0<1)


apartPow : ∀ x n →
  0ℝ #ℝ x →
  0ℝ #ℝ powℝ x n
apartPow x zero x-apart = apartOne
apartPow x (suc n) x-apart =
  apartMul x (powℝ x n) x-apart (apartPow x n x-apart)
