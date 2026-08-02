module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base

mulCommAtJointBound : ∀ (x y : ℝ) →
  JointNaturalAbsBounds x y →
  x · y ≡ y · x
mulCommAtJointBound x y w =
  multiplicationWithin B x y
    (jointBoundContainsLeft {x = x} {y = y} w)
    (jointBoundContainsRight {x = x} {y = y} w)
  ∙ boundedMulComm B x y
  ∙ sym
      (multiplicationWithin B y x
        (jointBoundContainsRight {x = x} {y = y} w)
        (jointBoundContainsLeft {x = x} {y = y} w))
  where
  B : ℚ₊
  B = jointBound {x = x} {y = y} w

mulComm : ∀ x y → x · y ≡ y · x
mulComm x y =
  PT.rec
    (isSetℝ _ _)
    (mulCommAtJointBound x y)
    (jointNaturalAbsBounds x y)

mulZeroRAtJointBound : ∀ (x : ℝ) →
  JointNaturalAbsBounds x 0 →
  x · 0 ≡ 0
mulZeroRAtJointBound x w =
  multiplicationWithin B x 0
    (jointBoundContainsLeft {x = x} {y = 0} w)
    (jointBoundContainsRight {x = x} {y = 0} w)
  ∙ boundedMulZeroR B x
  where
  B : ℚ₊
  B = jointBound {x = x} {y = 0} w

mulZeroR : ∀ x → x · 0 ≡ 0
mulZeroR x =
  PT.rec
    (isSetℝ _ _)
    (mulZeroRAtJointBound x)
    (jointNaturalAbsBounds x 0)

mulZeroL : ∀ x → 0 · x ≡ 0
mulZeroL x =
  mulComm 0 x
  ∙ mulZeroR x

private
  jointBoundAtLeastOne : ∀ (x : ℝ)
    (w : JointNaturalAbsBounds x 1) →
    1 ℚ.≤ fst (jointBound {x = x} {y = 1} w)
  jointBoundAtLeastOne x w =
    ≤ℝ→≤ℚ 1 (fst B)
      (≤ℝ-trans
        1 (absℝ 1) (rat (fst B))
        (leAbs 1)
        (jointBoundContainsRight {x = x} {y = 1} w))
    where
    B : ℚ₊
    B = jointBound {x = x} {y = 1} w

mulIdRAtJointBound : ∀ (x : ℝ) →
  JointNaturalAbsBounds x 1 →
  x · 1 ≡ x
mulIdRAtJointBound x w =
  multiplicationWithin B x 1 absx≤B abs1≤B
  ∙ boundedMulOneR B (jointBoundAtLeastOne x w) x
  ∙ clampFixpointFromAbs B x absx≤B
  where
  B : ℚ₊
  B = jointBound {x = x} {y = 1} w

  absx≤B : absℝ x ≤ℝ rat (fst B)
  absx≤B = jointBoundContainsLeft {x = x} {y = 1} w

  abs1≤B : absℝ 1 ≤ℝ rat (fst B)
  abs1≤B = jointBoundContainsRight {x = x} {y = 1} w

mulIdR : ∀ x → x · 1 ≡ x
mulIdR x =
  PT.rec
    (isSetℝ _ _)
    (mulIdRAtJointBound x)
    (jointNaturalAbsBounds x 1)

mulIdL : ∀ x → 1 · x ≡ x
mulIdL x =
  mulComm 1 x
  ∙ mulIdR x

mulAbs≤AtBound : ∀ (B : ℚ₊) (x y : ℝ) →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  absℝ (x · y) ≤ℝ rat (boundedSquare B)
mulAbs≤AtBound B x y absx≤B absy≤B =
  subst
    (_≤ℝ rat (boundedSquare B))
    (sym
      (cong absℝ
        (multiplicationWithin B x y absx≤B absy≤B)))
    (boundedMulAbs≤Square B x y)
