module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Division where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Positive
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Order

positiveDivideℝ : ℝ → (y : ℝ) → 0 <ℝ y → ℝ
positiveDivideℝ x y py =
  x · positiveReciprocal y py

positiveDivideMulR : ∀ x y (py : 0 <ℝ y) →
  positiveDivideℝ x y py · y ≡ x
positiveDivideMulR x y py =
  mulAssoc x (positiveReciprocal y py) y
  ∙ cong (x ·_)
      (positiveReciprocalLaw' y py)
  ∙ mulIdR x

mulPositiveDivide : ∀ x y (py : 0 <ℝ y) →
  y · positiveDivideℝ x y py ≡ x
mulPositiveDivide x y py =
  mulComm y (positiveDivideℝ x y py)
  ∙ positiveDivideMulR x y py

positiveDivideMulCancel : ∀ x y (py : 0 <ℝ y) →
  positiveDivideℝ (x · y) y py ≡ x
positiveDivideMulCancel x y py =
  mulAssoc x y (positiveReciprocal y py)
  ∙ cong (x ·_)
      (positiveReciprocalLaw y py)
  ∙ mulIdR x

private
  inverseMulProduct : ∀ z y (py : 0 <ℝ y) →
    positiveReciprocal y py · (y · z) ≡ z
  inverseMulProduct z y py =
    sym
      (mulAssoc
        (positiveReciprocal y py) y z)
    ∙ cong (_· z)
        (positiveReciprocalLaw' y py)
    ∙ mulIdL z

≤positiveDivideEquiv : ∀ x z y (py : 0 <ℝ y) →
  (z ≤ℝ positiveDivideℝ x y py) ≃
  (y · z ≤ℝ x)
≤positiveDivideEquiv x z y py =
  propBiimpl→Equiv
    (isProp≤ℝ z (positiveDivideℝ x y py))
    (isProp≤ℝ (y · z) x)
    forward backward
  where
  iy : ℝ
  iy =
    positiveReciprocal y py

  0≤y : 0 ≤ℝ y
  0≤y =
    <ℝ-weaken 0 y py

  0≤iy : 0 ≤ℝ iy
  0≤iy =
    <ℝ-weaken 0 iy
      (positiveReciprocalPositive y py)

  forward :
    z ≤ℝ positiveDivideℝ x y py →
    y · z ≤ℝ x
  forward z≤x/y =
    subst
      (y · z ≤ℝ_)
      (mulPositiveDivide x y py)
      (mulMonoL≤
        z (positiveDivideℝ x y py)
        y 0≤y z≤x/y)

  backward :
    y · z ≤ℝ x →
    z ≤ℝ positiveDivideℝ x y py
  backward yz≤x =
    subst2 _≤ℝ_
      (inverseMulProduct z y py)
      (mulComm iy x)
      (mulMonoL≤
        (y · z) x iy 0≤iy yz≤x)

<positiveDivideEquiv : ∀ x z y (py : 0 <ℝ y) →
  (z <ℝ positiveDivideℝ x y py) ≃
  (y · z <ℝ x)
<positiveDivideEquiv x z y py =
  propBiimpl→Equiv
    (isProp<ℝ z (positiveDivideℝ x y py))
    (isProp<ℝ (y · z) x)
    forward backward
  where
  iy : ℝ
  iy =
    positiveReciprocal y py

  0<iy : 0 <ℝ iy
  0<iy =
    positiveReciprocalPositive y py

  forward :
    z <ℝ positiveDivideℝ x y py →
    y · z <ℝ x
  forward z<x/y =
    subst
      (y · z <ℝ_)
      (mulPositiveDivide x y py)
      (mulMonoL<
        z (positiveDivideℝ x y py)
        y py z<x/y)

  backward :
    y · z <ℝ x →
    z <ℝ positiveDivideℝ x y py
  backward yz<x =
    subst2 _<ℝ_
      (inverseMulProduct z y py)
      (mulComm iy x)
      (mulMonoL<
        (y · z) x iy 0<iy yz<x)

positiveDivide≤Equiv : ∀ x z y (py : 0 <ℝ y) →
  (positiveDivideℝ x y py ≤ℝ z) ≃
  (x ≤ℝ y · z)
positiveDivide≤Equiv x z y py =
  propBiimpl→Equiv
    (isProp≤ℝ (positiveDivideℝ x y py) z)
    (isProp≤ℝ x (y · z))
    forward backward
  where
  iy : ℝ
  iy =
    positiveReciprocal y py

  0≤y : 0 ≤ℝ y
  0≤y =
    <ℝ-weaken 0 y py

  0≤iy : 0 ≤ℝ iy
  0≤iy =
    <ℝ-weaken 0 iy
      (positiveReciprocalPositive y py)

  forward :
    positiveDivideℝ x y py ≤ℝ z →
    x ≤ℝ y · z
  forward x/y≤z =
    subst2 _≤ℝ_
      (positiveDivideMulR x y py)
      (mulComm z y)
      (mulMonoR≤
        (positiveDivideℝ x y py) z
        y 0≤y x/y≤z)

  backward :
    x ≤ℝ y · z →
    positiveDivideℝ x y py ≤ℝ z
  backward x≤yz =
    subst2 _≤ℝ_
      (mulComm iy x)
      (inverseMulProduct z y py)
      (mulMonoL≤ x (y · z) iy 0≤iy x≤yz)

positiveDivide<Equiv : ∀ x z y (py : 0 <ℝ y) →
  (positiveDivideℝ x y py <ℝ z) ≃
  (x <ℝ y · z)
positiveDivide<Equiv x z y py =
  propBiimpl→Equiv
    (isProp<ℝ (positiveDivideℝ x y py) z)
    (isProp<ℝ x (y · z))
    forward backward
  where
  iy : ℝ
  iy =
    positiveReciprocal y py

  0<iy : 0 <ℝ iy
  0<iy =
    positiveReciprocalPositive y py

  forward :
    positiveDivideℝ x y py <ℝ z →
    x <ℝ y · z
  forward x/y<z =
    subst2 _<ℝ_
      (positiveDivideMulR x y py)
      (mulComm z y)
      (mulMonoR<
        (positiveDivideℝ x y py) z
        y py x/y<z)

  backward :
    x <ℝ y · z →
    positiveDivideℝ x y py <ℝ z
  backward x<yz =
    subst2 _<ℝ_
      (mulComm iy x)
      (inverseMulProduct z y py)
      (mulMonoL< x (y · z) iy 0<iy x<yz)
