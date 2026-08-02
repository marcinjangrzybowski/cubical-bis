module Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicativeApartness where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Apartness
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Structure
open import Cubical.HITs.CauchyRealsP.Algebra.Powers

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

negativeNegationPositive : ∀ {x} →
  x <ℝ 0 →
  0 <ℝ (- x)
negativeNegationPositive {x} x<0 =
  subst2 _<ℝ_ negZero refl
    (<ℝ-neg x 0 x<0)

positiveNegationNegative : ∀ {x} →
  0 <ℝ (- x) →
  x <ℝ 0
positiveNegationNegative {x} 0<-x =
  subst2 _<ℝ_ (negInvol x) negZero
    (<ℝ-neg 0 (- x) 0<-x)

negationOfPositiveNegative : ∀ {x} →
  0 <ℝ x →
  (- x) <ℝ 0
negationOfPositiveNegative {x} 0<x =
  subst2 _<ℝ_ refl negZero
    (<ℝ-neg 0 x 0<x)

apartMul : ∀ x y →
  0 ＃ x →
  0 ＃ y →
  0 ＃ (x · y)
apartMul x y (inl 0<x) (inl 0<y) =
  inl (mulPositive x y 0<x 0<y)
apartMul x y (inl 0<x) (inr y<0) =
  inr
    (positiveNegationNegative
      (subst
        (0 <ℝ_)
        (ℝRing.-DistR· x y)
        (mulPositive x (- y)
          0<x (negativeNegationPositive y<0))))
apartMul x y (inr x<0) (inl 0<y) =
  inr
    (positiveNegationNegative
      (subst
        (0 <ℝ_)
        (ℝRing.-DistL· x y)
        (mulPositive (- x) y
          (negativeNegationPositive x<0) 0<y)))
apartMul x y (inr x<0) (inr y<0) =
  inl
    (subst
      (0 <ℝ_)
      (ℝRing.-Dist· x y)
      (mulPositive (- x) (- y)
        (negativeNegationPositive x<0)
        (negativeNegationPositive y<0)))

apartOne : 0 ＃ 1
apartOne =
  inl (isOrderedCommRingℝ .IsOrderedCommRing.0<1)

apartPow : ∀ x n →
  0 ＃ x →
  0 ＃ (x ^ⁿ n)
apartPow x zero x-apart =
  apartOne
apartPow x (suc n) x-apart =
  apartMul
    x (x ^ⁿ n)
    x-apart (apartPow x n x-apart)
