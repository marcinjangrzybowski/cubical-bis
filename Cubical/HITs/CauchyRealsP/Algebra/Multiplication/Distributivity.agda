module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Distributivity where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.CommonBounds
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing

  addRealLipschitzWith :
    (f g : ℝ → ℝ) (K L : ℚ₊) →
    IsLipschitzWith
      (snd ℝPremetricSpace) f
      (snd ℝPremetricSpace) K →
    IsLipschitzWith
      (snd ℝPremetricSpace) g
      (snd ℝPremetricSpace) L →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → f x + g x)
      (snd ℝPremetricSpace) (K +₊ L)
  addRealLipschitzWith f g K L f-lip g-lip
    .IsLipschitzWith.pres≈ x y ε x∼y =
      subst∼
        (f x + g x) (f y + g y)
        {ε = (K ·₊ ε) +₊ (L ·₊ ε)}
        {ε' = (K +₊ L) ·₊ ε}
        ℚ!
        (addPres∼
          (f x) (f y) (g x) (g y)
          (K ·₊ ε) (L ·₊ ε)
          (IsLipschitzWith.pres≈ f-lip x y ε x∼y)
          (IsLipschitzWith.pres≈ g-lip x y ε x∼y))

clampedSumAbs≤Doubled : ∀ B q r →
  abs (clampAt B q ℚ.+ clampAt B r)
    ℚ.≤ fst (doubledBound B)
clampedSumAbs≤Doubled B q r =
  ℚ.isTrans≤
    (abs (clampAt B q ℚ.+ clampAt B r))
    (abs (clampAt B q) ℚ.+ abs (clampAt B r))
    (fst B ℚ.+ fst B)
    (ℚOrder.triangularInequality
      (clampAt B q) (clampAt B r))
    (ℚ.≤Monotone+
      (abs (clampAt B q)) (fst B)
      (abs (clampAt B r)) (fst B)
      (clampAtAbs≤ B q)
      (clampAtAbs≤ B r))

private
  distLeft : ℚ₊ → ℝ → ℝ → ℝ → ℝ
  distLeft B x y z =
    boundedMulℝ (doubledBound B)
      (clampℝ B x)
      (clampℝ B y + clampℝ B z)

  distRight : ℚ₊ → ℝ → ℝ → ℝ → ℝ
  distRight B x y z =
    boundedMulℝ B x y + boundedMulℝ B x z

  distLeftLip₁ : ∀ B y z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → distLeft B x y z)
      (snd ℝPremetricSpace) (doubledBound B)
  distLeftLip₁ B y z
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₁At
          (doubledBound B)
          (clampℝ B y + clampℝ B z))
        (clampℝ B x) (clampℝ B x') ε
        (clampPres∼ B x x' ε x∼x')

  distLeftLip₂ : ∀ B x z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ y → distLeft B x y z)
      (snd ℝPremetricSpace) (doubledBound B)
  distLeftLip₂ B x z
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₂
          (doubledBound B) (clampℝ B x))
        (clampℝ B y + clampℝ B z)
        (clampℝ B y' + clampℝ B z) ε
        (addPres∼₁
          (clampℝ B y) (clampℝ B y')
          (clampℝ B z) ε
          (clampPres∼ B y y' ε y∼y'))

  distLeftLip₃ : ∀ B x y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (distLeft B x y)
      (snd ℝPremetricSpace) (doubledBound B)
  distLeftLip₃ B x y
    .IsLipschitzWith.pres≈ z z' ε z∼z' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₂
          (doubledBound B) (clampℝ B x))
        (clampℝ B y + clampℝ B z)
        (clampℝ B y + clampℝ B z') ε
        (addPres∼₂
          (clampℝ B y)
          (clampℝ B z) (clampℝ B z') ε
          (clampPres∼ B z z' ε z∼z'))

  distRightLip₁ : ∀ B y z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → distRight B x y z)
      (snd ℝPremetricSpace) (doubledBound B)
  distRightLip₁ B y z =
    addRealLipschitzWith
      (λ x → boundedMulℝ B x y)
      (λ x → boundedMulℝ B x z)
      B B
      (boundedMulIsLipschitz₁At B y)
      (boundedMulIsLipschitz₁At B z)

  distRightLip₂ : ∀ B x z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ y → distRight B x y z)
      (snd ℝPremetricSpace) B
  distRightLip₂ B x z
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      addPres∼₁
        (boundedMulℝ B x y) (boundedMulℝ B x y')
        (boundedMulℝ B x z) (B ·₊ ε)
        (IsLipschitzWith.pres≈
          (boundedMulIsLipschitz₂ B x)
          y y' ε y∼y')

  distRightLip₃ : ∀ B x y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (distRight B x y)
      (snd ℝPremetricSpace) B
  distRightLip₃ B x y
    .IsLipschitzWith.pres≈ z z' ε z∼z' =
      addPres∼₂
        (boundedMulℝ B x y)
        (boundedMulℝ B x z) (boundedMulℝ B x z')
        (B ·₊ ε)
        (IsLipschitzWith.pres≈
          (boundedMulIsLipschitz₂ B x)
          z z' ε z∼z')

  distLeft-rat : ∀ B p q r →
    distLeft B (rat p) (rat q) (rat r) ≡
    rat
      (clampAt B p ℚ.·
        (clampAt B q ℚ.+ clampAt B r))
  distLeft-rat B p q r =
    cong₂ (boundedMulℝ C)
      (clamp-rat B p)
      (cong₂ _+_
        (clamp-rat B q)
        (clamp-rat B r)
        ∙ rat+rat (clampAt B q) (clampAt B r))
    ∙ boundedMul-rat-within C
        (clampAt B p)
        (clampAt B q ℚ.+ clampAt B r)
        (fst pInterval) (snd pInterval)
        (fst sumInterval) (snd sumInterval)
    where
    C : ℚ₊
    C = doubledBound B

    pAbs≤C : abs (clampAt B p) ℚ.≤ fst C
    pAbs≤C =
      ℚ.isTrans≤
        (abs (clampAt B p)) (fst B) (fst C)
        (clampAtAbs≤ B p)
        (bound≤Doubled B)

    pInterval =
      rationalAbsBound→Interval C (clampAt B p) pAbs≤C

    sumAbs≤C :
      abs (clampAt B q ℚ.+ clampAt B r) ℚ.≤ fst C
    sumAbs≤C = clampedSumAbs≤Doubled B q r

    sumInterval =
      rationalAbsBound→Interval C
        (clampAt B q ℚ.+ clampAt B r) sumAbs≤C

  distRight-rat : ∀ B p q r →
    distRight B (rat p) (rat q) (rat r) ≡
    rat
      ((clampAt B p ℚ.· clampAt B q) ℚ.+
       (clampAt B p ℚ.· clampAt B r))
  distRight-rat B p q r =
    cong₂ _+_
      (boundedMul-rat B p q)
      (boundedMul-rat B p r)
    ∙ rat+rat
        (clampAt B p ℚ.· clampAt B q)
        (clampAt B p ℚ.· clampAt B r)

boundedMulDistRClamped : ∀ B x y z →
  boundedMulℝ (doubledBound B)
    (clampℝ B x)
    (clampℝ B y + clampℝ B z)
  ≡
  boundedMulℝ B x y + boundedMulℝ B x z
boundedMulDistRClamped B =
  lipschitzExtensionality₃
    (distLeft B) (distRight B)
    (λ y z → ∣ doubledBound B , distLeftLip₁ B y z ∣₁)
    (λ x z → ∣ doubledBound B , distLeftLip₂ B x z ∣₁)
    (λ x y → ∣ doubledBound B , distLeftLip₃ B x y ∣₁)
    (λ y z → ∣ doubledBound B , distRightLip₁ B y z ∣₁)
    (λ x z → ∣ B , distRightLip₂ B x z ∣₁)
    (λ x y → ∣ B , distRightLip₃ B x y ∣₁)
    λ p q r →
      distLeft-rat B p q r
      ∙ cong rat
          (ℚ.·DistL+
            (clampAt B p)
            (clampAt B q)
            (clampAt B r))
      ∙ sym (distRight-rat B p q r)

boundedMulDistRWithin : ∀ B x y z →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  absℝ z ≤ℝ rat (fst B) →
  boundedMulℝ (doubledBound B) x (y + z) ≡
  boundedMulℝ B x y + boundedMulℝ B x z
boundedMulDistRWithin B x y z absx≤B absy≤B absz≤B =
  sym
    (cong₂
      (boundedMulℝ (doubledBound B))
      (clampFixpointFromAbs B x absx≤B)
      (cong₂ _+_
        (clampFixpointFromAbs B y absy≤B)
        (clampFixpointFromAbs B z absz≤B)))
  ∙ boundedMulDistRClamped B x y z

sumAbs≤Doubled : ∀ B y z →
  absℝ y ≤ℝ rat (fst B) →
  absℝ z ≤ℝ rat (fst B) →
  absℝ (y + z) ≤ℝ rat (fst (doubledBound B))
sumAbs≤Doubled B y z absy≤B absz≤B =
  subst
    (absℝ (y + z) ≤ℝ_)
    (rat+rat (fst B) (fst B))
    (≤ℝ-trans
      (absℝ (y + z))
      (absℝ y + absℝ z)
      (rat (fst B) + rat (fst B))
      (absTriangle y z)
      (≤ℝ-add
        (absℝ y) (rat (fst B))
        (absℝ z) (rat (fst B))
        absy≤B absz≤B))

mulDistRAtTripleBound : ∀ (x y z : ℝ) →
  TripleNaturalAbsBounds x y z →
  x · (y + z) ≡ (x · y) + (x · z)
mulDistRAtTripleBound x y z w =
  multiplicationWithin C x (y + z) absx≤C abssum≤C
  ∙ boundedMulDistRWithin B x y z absx≤B absy≤B absz≤B
  ∙ cong₂ _+_
      (sym (multiplicationWithin B x y absx≤B absy≤B))
      (sym (multiplicationWithin B x z absx≤B absz≤B))
  where
  B : ℚ₊
  B = tripleBound {x = x} {y = y} {z = z} w

  C : ℚ₊
  C = doubledBound B

  absx≤B : absℝ x ≤ℝ rat (fst B)
  absx≤B =
    tripleBoundContains₁ {x = x} {y = y} {z = z} w

  absy≤B : absℝ y ≤ℝ rat (fst B)
  absy≤B =
    tripleBoundContains₂ {x = x} {y = y} {z = z} w

  absz≤B : absℝ z ≤ℝ rat (fst B)
  absz≤B =
    tripleBoundContains₃ {x = x} {y = y} {z = z} w

  absx≤C : absℝ x ≤ℝ rat (fst C)
  absx≤C =
    ≤ℝ-trans
      (absℝ x) (rat (fst B)) (rat (fst C))
      absx≤B
      (≤ℚ→≤ℝ (fst B) (fst C) (bound≤Doubled B))

  abssum≤C : absℝ (y + z) ≤ℝ rat (fst C)
  abssum≤C = sumAbs≤Doubled B y z absy≤B absz≤B

mulDistR : ∀ (x y z : ℝ) →
  x · (y + z) ≡ (x · y) + (x · z)
mulDistR x y z =
  PT.rec
    (isSetℝ _ _)
    (mulDistRAtTripleBound x y z)
    (tripleNaturalAbsBounds x y z)

mulDistL : ∀ (x y z : ℝ) →
  (x + y) · z ≡ (x · z) + (y · z)
mulDistL x y z =
  mulComm (x + y) z
  ∙ mulDistR z x y
  ∙ cong₂ _+_ (mulComm z x) (mulComm z y)
