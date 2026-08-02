module Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing

open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  clampAtNonnegative : ∀ B q →
    0 ℚ.≤ q → 0 ℚ.≤ clampAt B q
  clampAtNonnegative B q 0≤q =
    subst
      (ℚ._≤ clampAt B q)
      (clampAtZero B)
      (ℚ.≤MonotoneClamp
        (ℚ.- fst B) (fst B) 0 q 0≤q)

  boundedNonnegativeRight : ℚ₊ → ℝ → ℝ → ℝ
  boundedNonnegativeRight B x y =
    boundedMulℝ B (maxℝ 0 x) (maxℝ 0 y)

  boundedNonnegativeLeft : ℚ₊ → ℝ → ℝ → ℝ
  boundedNonnegativeLeft B x y =
    maxℝ 0 (boundedNonnegativeRight B x y)

  boundedNonnegativeRightLip₁ : ∀ B y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → boundedNonnegativeRight B x y)
      (snd ℝPremetricSpace) B
  boundedNonnegativeRightLip₁ B y
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₁At B (maxℝ 0 y))
        (maxℝ 0 x) (maxℝ 0 x') ε
        (maxPres∼₂ 0 x x' ε x∼x')

  boundedNonnegativeRightLip₂ : ∀ B x →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (boundedNonnegativeRight B x)
      (snd ℝPremetricSpace) B
  boundedNonnegativeRightLip₂ B x
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₂ B (maxℝ 0 x))
        (maxℝ 0 y) (maxℝ 0 y') ε
        (maxPres∼₂ 0 y y' ε y∼y')

  boundedNonnegativeLeftLip₁ : ∀ B y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → boundedNonnegativeLeft B x y)
      (snd ℝPremetricSpace) B
  boundedNonnegativeLeftLip₁ B y
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      maxPres∼₂
        0
        (boundedNonnegativeRight B x y)
        (boundedNonnegativeRight B x' y)
        (B ·₊ ε)
        (IsLipschitzWith.pres≈
          (boundedNonnegativeRightLip₁ B y)
          x x' ε x∼x')

  boundedNonnegativeLeftLip₂ : ∀ B x →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (boundedNonnegativeLeft B x)
      (snd ℝPremetricSpace) B
  boundedNonnegativeLeftLip₂ B x
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      maxPres∼₂
        0
        (boundedNonnegativeRight B x y)
        (boundedNonnegativeRight B x y')
        (B ·₊ ε)
        (IsLipschitzWith.pres≈
          (boundedNonnegativeRightLip₂ B x)
          y y' ε y∼y')

  boundedNonnegativeRight-rat : ∀ B p q →
    boundedNonnegativeRight B (rat p) (rat q) ≡
    rat
      (clampAt B (ℚ.max 0 p) ℚ.·
       clampAt B (ℚ.max 0 q))
  boundedNonnegativeRight-rat B p q =
    cong₂ (boundedMulℝ B)
      (max-rat 0 p)
      (max-rat 0 q)
    ∙ boundedMul-rat B (ℚ.max 0 p) (ℚ.max 0 q)

  boundedMulNonnegativeMax-rat : ∀ B p q →
    boundedNonnegativeLeft B (rat p) (rat q) ≡
    boundedNonnegativeRight B (rat p) (rat q)
  boundedMulNonnegativeMax-rat B p q =
    cong (maxℝ 0) (boundedNonnegativeRight-rat B p q)
    ∙ max-rat 0 product
    ∙ cong rat (ℚ.≤→max 0 product productNonnegative)
    ∙ sym (boundedNonnegativeRight-rat B p q)
    where
    product : ℚ
    product =
      clampAt B (ℚ.max 0 p) ℚ.·
      clampAt B (ℚ.max 0 q)

    leftNonnegative :
      0 ℚ.≤ clampAt B (ℚ.max 0 p)
    leftNonnegative =
      clampAtNonnegative B (ℚ.max 0 p) (ℚ.≤max 0 p)

    rightNonnegative :
      0 ℚ.≤ clampAt B (ℚ.max 0 q)
    rightNonnegative =
      clampAtNonnegative B (ℚ.max 0 q) (ℚ.≤max 0 q)

    productNonnegative : 0 ℚ.≤ product
    productNonnegative =
      NonNegativeRationals.0≤·Closed
        (clampAt B (ℚ.max 0 p))
        (clampAt B (ℚ.max 0 q))
        leftNonnegative rightNonnegative

boundedMulNonnegativeMax : ∀ B x y →
  maxℝ 0 (boundedMulℝ B (maxℝ 0 x) (maxℝ 0 y)) ≡
  boundedMulℝ B (maxℝ 0 x) (maxℝ 0 y)
boundedMulNonnegativeMax B =
  lipschitzExtensionality₂
    (boundedNonnegativeLeft B)
    (boundedNonnegativeRight B)
    (λ y → ∣ B , boundedNonnegativeLeftLip₁ B y ∣₁)
    (λ x → ∣ B , boundedNonnegativeLeftLip₂ B x ∣₁)
    (λ y → ∣ B , boundedNonnegativeRightLip₁ B y ∣₁)
    (λ x → ∣ B , boundedNonnegativeRightLip₂ B x ∣₁)
    (boundedMulNonnegativeMax-rat B)

boundedMulNonnegative : ∀ B x y →
  0 ≤ℝ x → 0 ≤ℝ y →
  0 ≤ℝ boundedMulℝ B x y
boundedMulNonnegative B x y 0≤x 0≤y =
  maxPath→≤ℝ 0 (boundedMulℝ B x y)
    (subst
      (λ u → maxℝ 0 u ≡ u)
      (cong₂
        (boundedMulℝ B)
        (maxOf≤ 0 x 0≤x)
        (maxOf≤ 0 y 0≤y))
      (boundedMulNonnegativeMax B x y))

mulNonnegativeAtJointBound : ∀ (x y : ℝ) →
  JointNaturalAbsBounds x y →
  0 ≤ℝ x → 0 ≤ℝ y →
  0 ≤ℝ x · y
mulNonnegativeAtJointBound x y w 0≤x 0≤y =
  subst
    (0 ≤ℝ_)
    (sym
      (multiplicationWithin B x y
        (jointBoundContainsLeft {x = x} {y = y} w)
        (jointBoundContainsRight {x = x} {y = y} w)))
    (boundedMulNonnegative B x y 0≤x 0≤y)
  where
  B : ℚ₊
  B = jointBound {x = x} {y = y} w

mulNonnegative : ∀ x y →
  0 ≤ℝ x → 0 ≤ℝ y →
  0 ≤ℝ x · y
mulNonnegative x y 0≤x 0≤y =
  PT.rec
    (isProp≤ℝ 0 (x · y))
    (λ w → mulNonnegativeAtJointBound x y w 0≤x 0≤y)
    (jointNaturalAbsBounds x y)

mulMonoR≤ : ∀ x y z →
  0 ≤ℝ z → x ≤ℝ y →
  x · z ≤ℝ y · z
mulMonoR≤ x y z 0≤z x≤y =
  nonnegativeSub→≤ (x · z) (y · z)
    (subst
      (0 ≤ℝ_)
      (ℝRing.·DistL- y x z)
      (mulNonnegative (y - x) z
        (nonnegativeSub x y x≤y) 0≤z))

mulMonoL≤ : ∀ x y z →
  0 ≤ℝ z → x ≤ℝ y →
  z · x ≤ℝ z · y
mulMonoL≤ x y z 0≤z x≤y =
  subst2 _≤ℝ_
    (mulComm x z)
    (mulComm y z)
    (mulMonoR≤ x y z 0≤z x≤y)

mulMono≤ : ∀ x y z w →
  0 ≤ℝ y → 0 ≤ℝ z →
  x ≤ℝ y → z ≤ℝ w →
  x · z ≤ℝ y · w
mulMono≤ x y z w 0≤y 0≤z x≤y z≤w =
  ≤ℝ-trans
    (x · z) (y · z) (y · w)
    (mulMonoR≤ x y z 0≤z x≤y)
    (mulMonoL≤ z w y 0≤y z≤w)

mulPositive : ∀ x y →
  0 <ℝ x → 0 <ℝ y →
  0 <ℝ x · y
mulPositive x y 0<x 0<y =
  PT.rec
    (isProp<ℝ 0 (x · y))
    (λ u →
      PT.rec
        (isProp<ℝ 0 (x · y))
        (positiveFromGaps u)
        0<y)
    0<x
  where
  positiveFromGaps :
    PositiveGap 0 x → PositiveGap 0 y →
    0 <ℝ x · y
  positiveFromGaps u v =
    result
    where
    δ ε : ℚ₊
    δ = width u
    ε = width v

    ratδ≤x : rat (fst δ) ≤ℝ x
    ratδ≤x =
      subst (_≤ℝ x)
        (addIdL (rat (fst δ)))
        (gapBoundElim 0 x δ (bound u))

    ratε≤y : rat (fst ε) ≤ℝ y
    ratε≤y =
      subst (_≤ℝ y)
        (addIdL (rat (fst ε)))
        (gapBoundElim 0 y ε (bound v))

    0≤x : 0 ≤ℝ x
    0≤x = <ℝ-weaken 0 x ∣ u ∣₁

    0≤ratε : 0 ≤ℝ rat (fst ε)
    0≤ratε =
      ≤ℚ→≤ℝ 0 (fst ε)
        (ℚ.<Weaken≤ 0 (fst ε) (snd ε))

    rationalProduct≤ :
      rat (fst δ) · rat (fst ε) ≤ℝ x · y
    rationalProduct≤ =
      mulMono≤
        (rat (fst δ)) x
        (rat (fst ε)) y
        0≤x 0≤ratε ratδ≤x ratε≤y

    productPositive :
      0 <ℝ rat (fst (δ ·₊ ε))
    productPositive =
      <ℚ→<ℝ 0 (fst (δ ·₊ ε)) (snd (δ ·₊ ε))

    result : 0 <ℝ x · y
    result =
      <≤ℝ-trans
        0 (rat (fst (δ ·₊ ε))) (x · y)
        productPositive
        (subst
          (_≤ℝ x · y)
          (mul-rat (fst δ) (fst ε))
          rationalProduct≤)

mulMonoR< : ∀ x y z →
  0 <ℝ z → x <ℝ y →
  x · z <ℝ y · z
mulMonoR< x y z 0<z x<y =
  positiveSub→< (x · z) (y · z)
    (subst
      (0 <ℝ_)
      (ℝRing.·DistL- y x z)
      (mulPositive (y - x) z
        (positiveSub x y x<y) 0<z))

mulMonoL< : ∀ x y z →
  0 <ℝ z → x <ℝ y →
  z · x <ℝ z · y
mulMonoL< x y z 0<z x<y =
  subst2 _<ℝ_
    (mulComm x z)
    (mulComm y z)
    (mulMonoR< x y z 0<z x<y)
