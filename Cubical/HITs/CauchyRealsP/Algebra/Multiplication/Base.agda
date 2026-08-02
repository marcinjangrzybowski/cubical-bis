module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Archimedean
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing

JointNaturalAbsBounds : ℝ → ℝ → Type
JointNaturalAbsBounds x y =
  NaturalAbsBound x × NaturalAbsBound y

jointNaturalAbsBounds : ∀ (x y : ℝ) →
  ∥ JointNaturalAbsBounds x y ∥₁
jointNaturalAbsBounds x y =
  PT.map2 _,_
    (∃naturalAbsBound x)
    (∃naturalAbsBound y)

jointBound : ∀ {x y : ℝ} →
  JointNaturalAbsBounds x y → ℚ₊
jointBound w =
  ℚ.maxWithPos
    (naturalBound (fst (fst w)))
    (naturalRational (fst (snd w)))

jointBoundContainsLeft : ∀ {x y : ℝ}
  (w : JointNaturalAbsBounds x y) →
  absℝ x ≤ℝ rat (fst (jointBound {x = x} {y = y} w))
jointBoundContainsLeft {x} {y} w =
  ≤ℝ-trans
    (absℝ x) (rat (naturalRational n))
    (rat (fst (ℚ.maxWithPos
      (naturalBound n) (naturalRational m))))
    (<ℝ-weaken
      (absℝ x) (rat (naturalRational n)) absx<n)
    (≤ℚ→≤ℝ
      (naturalRational n)
      (fst (ℚ.maxWithPos
        (naturalBound n) (naturalRational m)))
      (ℚ.≤max (naturalRational n) (naturalRational m)))
  where
  n m : ℕ₊₁
  n = fst (fst w)
  m = fst (snd w)

  absx<n : absℝ x <ℝ rat (naturalRational n)
  absx<n = snd (fst w)

jointBoundContainsRight : ∀ {x y : ℝ}
  (w : JointNaturalAbsBounds x y) →
  absℝ y ≤ℝ rat (fst (jointBound {x = x} {y = y} w))
jointBoundContainsRight {x} {y} w =
  ≤ℝ-trans
    (absℝ y) (rat (naturalRational m))
    (rat (fst (ℚ.maxWithPos
      (naturalBound n) (naturalRational m))))
    (<ℝ-weaken
      (absℝ y) (rat (naturalRational m)) absy<m)
    (≤ℚ→≤ℝ
      (naturalRational m)
      (fst (ℚ.maxWithPos
        (naturalBound n) (naturalRational m)))
      (ℚ.≤max' (naturalRational n) (naturalRational m)))
  where
  n m : ℕ₊₁
  n = fst (fst w)
  m = fst (snd w)

  absy<m : absℝ y <ℝ rat (naturalRational m)
  absy<m = snd (snd w)

private
  multiplicationAtBound : ∀ (x y : ℝ) →
    JointNaturalAbsBounds x y → ℝ
  multiplicationAtBound x y w =
    boundedMulℝ (jointBound {x = x} {y = y} w) x y

  multiplicationAtBoundConstant : ∀ (x y : ℝ) →
    2-Constant (multiplicationAtBound x y)
  multiplicationAtBoundConstant x y w v =
    let
      B : ℚ₊
      B = jointBound {x = x} {y = y} w

      C : ℚ₊
      C = jointBound {x = x} {y = y} v

      D : ℚ₊
      D = ℚ.maxWithPos B (fst C)

      B≤D : fst B ℚ.≤ fst D
      B≤D = ℚ.≤max (fst B) (fst C)

      C≤D : fst C ℚ.≤ fst D
      C≤D = ℚ.≤max' (fst B) (fst C)
    in
      sym
        (boundedMulAgreeWithinAbs B D B≤D x y
          (jointBoundContainsLeft {x = x} {y = y} w)
          (jointBoundContainsRight {x = x} {y = y} w))
      ∙ boundedMulAgreeWithinAbs C D C≤D x y
          (jointBoundContainsLeft {x = x} {y = y} v)
          (jointBoundContainsRight {x = x} {y = y} v)

infixl 7 _·_

opaque
  _·_ : ℝ → ℝ → ℝ
  x · y =
    PT.rec→Set isSetℝ
      (multiplicationAtBound x y)
      (multiplicationAtBoundConstant x y)
      (jointNaturalAbsBounds x y)

  multiplicationAtAnyBound : ∀ (x y : ℝ)
    (w : JointNaturalAbsBounds x y) →
    x · y ≡
    boundedMulℝ (jointBound {x = x} {y = y} w) x y
  multiplicationAtAnyBound x y w =
    PT.SetElim.helper isSetℝ
      (multiplicationAtBound x y)
      (multiplicationAtBoundConstant x y)
      (jointNaturalAbsBounds x y)
      ∣ w ∣₁

multiplicationAtRequestedBound :
  ∀ (B : ℚ₊) (x y : ℝ) →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  JointNaturalAbsBounds x y →
  x · y ≡ boundedMulℝ B x y
multiplicationAtRequestedBound B x y absx≤B absy≤B w =
  multiplicationAtAnyBound x y w
  ∙ jointToCommon
  ∙ commonToRequested
  where
  jointB : ℚ₊
  jointB = jointBound {x = x} {y = y} w

  commonB : ℚ₊
  commonB = ℚ.maxWithPos jointB (fst B)

  jointB≤commonB : fst jointB ℚ.≤ fst commonB
  jointB≤commonB = ℚ.≤max (fst jointB) (fst B)

  B≤commonB : fst B ℚ.≤ fst commonB
  B≤commonB = ℚ.≤max' (fst jointB) (fst B)

  jointToCommon :
    boundedMulℝ jointB x y ≡ boundedMulℝ commonB x y
  jointToCommon =
    sym
      (boundedMulAgreeWithinAbs
        jointB commonB jointB≤commonB x y
        (jointBoundContainsLeft {x = x} {y = y} w)
        (jointBoundContainsRight {x = x} {y = y} w))

  commonToRequested :
    boundedMulℝ commonB x y ≡ boundedMulℝ B x y
  commonToRequested =
    boundedMulAgreeWithinAbs B commonB B≤commonB x y
      absx≤B absy≤B

multiplicationWithin : ∀ (B : ℚ₊) (x y : ℝ) →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  x · y ≡ boundedMulℝ B x y
multiplicationWithin B x y absx≤B absy≤B =
  PT.rec
    (isSetℝ _ _)
    (multiplicationAtRequestedBound B x y absx≤B absy≤B)
    (jointNaturalAbsBounds x y)

private
  rationalBounds : ∀ q r →
    JointNaturalAbsBounds (rat q) (rat r)
  rationalBounds q r =
    rationalNaturalAbsBound q , rationalNaturalAbsBound r

  rationalBound : ℚ → ℚ → ℚ₊
  rationalBound q r =
    jointBound {x = rat q} {y = rat r} (rationalBounds q r)

  rationalAbs≤JointLeft : ∀ q r →
    abs q ℚ.≤ fst (rationalBound q r)
  rationalAbs≤JointLeft q r =
    ≤ℝ→≤ℚ (abs q) (fst B)
      (subst
        (_≤ℝ rat (fst B))
        (abs-rat q)
        (jointBoundContainsLeft
          {x = rat q} {y = rat r} (rationalBounds q r)))
    where
    B : ℚ₊
    B = rationalBound q r

  rationalAbs≤JointRight : ∀ q r →
    abs r ℚ.≤ fst (rationalBound q r)
  rationalAbs≤JointRight q r =
    ≤ℝ→≤ℚ (abs r) (fst B)
      (subst
        (_≤ℝ rat (fst B))
        (abs-rat r)
        (jointBoundContainsRight
          {x = rat q} {y = rat r} (rationalBounds q r)))
    where
    B : ℚ₊
    B = rationalBound q r

  rationalLowerFromAbs : ∀ (B : ℚ₊) (q : ℚ) →
    abs q ℚ.≤ fst B →
    ℚ.- fst B ℚ.≤ q
  rationalLowerFromAbs B q absq≤B =
    ℚ.isTrans≤
      (ℚ.- fst B) (ℚ.- abs q) q
      (ℚ.minus-≤ (abs q) (fst B) absq≤B)
      (subst
        (ℚ.- abs q ℚ.≤_)
        (ℚ.-Invol q)
        (ℚ.minus-≤
          (ℚ.- q) (abs q) (ℚOrder.-≤abs q)))

  rationalUpperFromAbs : ∀ (B : ℚ₊) (q : ℚ) →
    abs q ℚ.≤ fst B →
    q ℚ.≤ fst B
  rationalUpperFromAbs B q absq≤B =
    ℚ.isTrans≤ q (abs q) (fst B)
      (ℚOrder.≤abs q) absq≤B

mul-rat : ∀ (q r : ℚ) → rat q · rat r ≡ rat (q ℚ.· r)
mul-rat q r =
  multiplicationAtAnyBound
    (rat q) (rat r) (rationalBounds q r)
  ∙ boundedMul-rat-within B q r
      (rationalLowerFromAbs B q
        (rationalAbs≤JointLeft q r))
      (rationalUpperFromAbs B q
        (rationalAbs≤JointLeft q r))
      (rationalLowerFromAbs B r
        (rationalAbs≤JointRight q r))
      (rationalUpperFromAbs B r
        (rationalAbs≤JointRight q r))
  where
  B : ℚ₊
  B = rationalBound q r
