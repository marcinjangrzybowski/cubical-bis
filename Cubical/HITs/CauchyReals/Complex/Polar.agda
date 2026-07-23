module Cubical.HITs.CauchyReals.Complex.Polar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (_＃_; invℝ; invℝ≡; invℝ-pos; x·invℝ[x])
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Positive
open import Cubical.HITs.CauchyReals.Complex.UnitCircle


ℂˣ : Type
ℂˣ = Σ[ z ∈ ℂ ] 0ℂ #ℂ z


Polarℂ : Type
Polarℂ = ℝ₊ × UnitCircleℂ


ℂˣ≡ : ∀ {z w : ℂˣ} → fst z ≡ fst w → z ≡ w
ℂˣ≡ = Σ≡Prop (isProp#ℂ 0ℂ)


scaleℂ : ℝ → ℂ → ℂ
scaleℂ r z = fromℝ r ·ℂ z


opaque
  scaleℂ-path : ∀ r z → scaleℂ r z ≡ fromℝ r ·ℂ z
  scaleℂ-path r z = refl


opaque
  modulus-scale-unfold : ∀ r z →
    modulus (scaleℂ r z) ≡ modulus (fromℝ r ·ℂ z)
  modulus-scale-unfold r z = cong modulus (scaleℂ-path r z)


opaque
  modulus-scale-product : ∀ r z →
    modulus (scaleℂ r z) ≡ modulus (fromℝ r) ·ᵣ modulus z
  modulus-scale-product r z =
    modulus-scale-unfold r z ∙ modulus-mul (fromℝ r) z


opaque
  modulus-scale-factor : ∀ r z →
    modulus (fromℝ r) ·ᵣ modulus z ≡ absᵣ r ·ᵣ modulus z
  modulus-scale-factor r z =
    cong (_·ᵣ modulus z) (modulus-fromℝ r)


opaque
  modulus-scale : ∀ r z →
    modulus (scaleℂ r z) ≡ absᵣ r ·ᵣ modulus z
  modulus-scale r z =
    modulus-scale-product r z ∙ modulus-scale-factor r z

opaque
  modulus-scale-positive-factor : ∀ (r : ℝ₊) z →
    absᵣ (fst r) ·ᵣ modulus z ≡ fst r ·ᵣ modulus z
  modulus-scale-positive-factor r z =
    cong (_·ᵣ modulus z) (absᵣPos (fst r) (snd r))


opaque
  modulus-scale-positive : ∀ (r : ℝ₊) z →
    modulus (scaleℂ (fst r) z) ≡ fst r ·ᵣ modulus z
  modulus-scale-positive r z =
    modulus-scale (fst r) z ∙ modulus-scale-positive-factor r z


opaque
  unitCircle-modulus : ∀ (u : UnitCircleℂ) → modulus (fst u) ≡ 1
  unitCircle-modulus u = normSqOne→modulusOne (fst u) (snd u)


opaque
  modulus-scale-unit-middle : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    fst r ·ᵣ modulus (fst u) ≡ fst r ·ᵣ 1
  modulus-scale-unit-middle r u =
    cong (fst r ·ᵣ_) (unitCircle-modulus u)


opaque
  modulus-scale-unit-end : ∀ (r : ℝ₊) → fst r ·ᵣ 1 ≡ fst r
  modulus-scale-unit-end r = ·IdR (fst r)


opaque
  modulus-scale-unit : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    modulus (scaleℂ (fst r) (fst u)) ≡ fst r
  modulus-scale-unit r u =
    modulus-scale-positive r (fst u)
    ∙ modulus-scale-unit-middle r u
    ∙ modulus-scale-unit-end r

directionValue : (z : ℂ) → 0ℂ #ℂ z → ℂ
directionValue z 0#z =
  scaleℂ (invℝ (modulus z) (0#modulus 0#z)) z


opaque
  directionValue-path : ∀ z (0#z : 0ℂ #ℂ z) →
    directionValue z 0#z ≡
      scaleℂ (invℝ (modulus z) (0#modulus 0#z)) z
  directionValue-path z 0#z = refl


opaque
  modulus-scale-along-path : ∀ w r z → w ≡ scaleℂ r z →
    modulus w ≡ absᵣ r ·ᵣ modulus z
  modulus-scale-along-path w r z w≡rz =
    cong modulus w≡rz ∙ modulus-scale r z


opaque
  direction-modulus-scale : ∀ z (0#z : 0ℂ #ℂ z) →
    modulus (directionValue z 0#z) ≡
      absᵣ (invℝ (modulus z) (0#modulus 0#z)) ·ᵣ modulus z
  direction-modulus-scale z 0#z = modulus-scale-along-path
    (directionValue z 0#z)
    (invℝ (modulus z) (0#modulus 0#z)) z
    (directionValue-path z 0#z)


opaque
  inverse-positive-with-apart : ∀ (x : ℝ) (0#x : rat 0 ＃ x) →
    0 <ᵣ x → 0 <ᵣ invℝ x 0#x
  inverse-positive-with-apart x 0#x 0<x =
    subst (0 <ᵣ_)
      (sym (invℝ≡ x 0#x (inl 0<x)))
      (invℝ-pos x 0<x)


opaque
  abs-inverse-times-self : ∀ (x : ℝ) (0#x : rat 0 ＃ x) →
    0 <ᵣ x → absᵣ (invℝ x 0#x) ·ᵣ x ≡ invℝ x 0#x ·ᵣ x
  abs-inverse-times-self x 0#x 0<x =
    cong (_·ᵣ x)
      (absᵣPos (invℝ x 0#x)
        (inverse-positive-with-apart x 0#x 0<x))


opaque
  direction-positive-inverse : ∀ z (0#z : 0ℂ #ℂ z) →
    absᵣ (invℝ (modulus z) (0#modulus 0#z)) ·ᵣ modulus z ≡
      invℝ (modulus z) (0#modulus 0#z) ·ᵣ modulus z
  direction-positive-inverse z 0#z =
    abs-inverse-times-self (modulus z) (0#modulus 0#z)
      (0#ℂ→0<modulus 0#z)


opaque
  inverse-times-self : ∀ (x : ℝ) (0#x : rat 0 ＃ x) →
    invℝ x 0#x ·ᵣ x ≡ 1
  inverse-times-self x 0#x =
    ·ᵣComm (invℝ x 0#x) x ∙ x·invℝ[x] x 0#x


opaque
  directionModulusOne : ∀ z (0#z : 0ℂ #ℂ z) →
    modulus (directionValue z 0#z) ≡ 1
  directionModulusOne z 0#z =
    direction-modulus-scale z 0#z
    ∙ direction-positive-inverse z 0#z
    ∙ inverse-times-self (modulus z) (0#modulus 0#z)

unitDirection : (z : ℂ) → 0ℂ #ℂ z → UnitCircleℂ
unitDirection z 0#z = unitModulus→unitCircle
  (directionValue z 0#z , directionModulusOne z 0#z)


polarRadius : ℂˣ → ℝ₊
polarRadius (z , 0#z) = modulus z , 0#ℂ→0<modulus 0#z


polarCoordinates : ℂˣ → Polarℂ
polarCoordinates (z , 0#z) = polarRadius (z , 0#z) , unitDirection z 0#z


opaque
  positive-left-of-equal : ∀ x y → x ≡ y → 0 <ᵣ y → 0 <ᵣ x
  positive-left-of-equal x y x≡y = subst (0 <ᵣ_) (sym x≡y)


opaque
  positive-scaled-unit-from-path : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    modulus (scaleℂ (fst r) (fst u)) ≡ fst r →
    0 <ᵣ modulus (scaleℂ (fst r) (fst u))
  positive-scaled-unit-from-path r u modulus≡r =
    positive-left-of-equal
      (modulus (scaleℂ (fst r) (fst u))) (fst r)
      modulus≡r (snd r)


opaque
  fromPolarModulusPositive : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    0 <ᵣ modulus (scaleℂ (fst r) (fst u))
  fromPolarModulusPositive r u =
    positive-scaled-unit-from-path r u (modulus-scale-unit r u)


opaque
  apart-from-positive-modulus : ∀ z → 0 <ᵣ modulus z → 0ℂ #ℂ z
  apart-from-positive-modulus z = 0<modulus→0#ℂ


opaque
  fromPolarApart : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    0ℂ #ℂ scaleℂ (fst r) (fst u)
  fromPolarApart r u =
    apart-from-positive-modulus (scaleℂ (fst r) (fst u))
      (fromPolarModulusPositive r u)


fromPolar : Polarℂ → ℂˣ
fromPolar (r , u) =
  scaleℂ (fst r) (fst u) , fromPolarApart r u


opaque
  unitDirection-value : ∀ z (0#z : 0ℂ #ℂ z) →
    fst (unitDirection z 0#z) ≡ directionValue z 0#z
  unitDirection-value z 0#z = refl


opaque
  scale-scale-path : ∀ r s z →
    scaleℂ r (scaleℂ s z) ≡ fromℝ r ·ℂ (fromℝ s ·ℂ z)
  scale-scale-path r s z = refl


opaque
  reconstruct-scaled-inverse-algebra : ∀ r s z →
    r ·ᵣ s ≡ 1 → fromℝ r ·ℂ (fromℝ s ·ℂ z) ≡ z
  reconstruct-scaled-inverse-algebra r s z rs≡1 =
    ·ℂAssoc (fromℝ r) (fromℝ s) z
    ∙ cong (_·ℂ z) (sym (fromℝ-pres· r s))
    ∙ cong (λ q → fromℝ q ·ℂ z) rs≡1
    ∙ Cℂ.·IdL z


opaque
  reconstruct-scaled-inverse : ∀ r s z →
    r ·ᵣ s ≡ 1 → scaleℂ r (scaleℂ s z) ≡ z
  reconstruct-scaled-inverse r s z rs≡1 =
    scale-scale-path r s z
    ∙ reconstruct-scaled-inverse-algebra r s z rs≡1


opaque
  polarReconstruct : ∀ z (0#z : 0ℂ #ℂ z) →
    scaleℂ (modulus z) (fst (unitDirection z 0#z)) ≡ z
  polarReconstruct z 0#z =
    cong (scaleℂ (modulus z)) (unitDirection-value z 0#z)
    ∙ cong (scaleℂ (modulus z)) (directionValue-path z 0#z)
    ∙ reconstruct-scaled-inverse
        (modulus z) (invℝ (modulus z) (0#modulus 0#z)) z
        (x·invℝ[x] (modulus z) (0#modulus 0#z))


opaque
  fromPolar-value : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    fst (fromPolar (r , u)) ≡ scaleℂ (fst r) (fst u)
  fromPolar-value r u = refl


opaque
  fromPolar-modulus : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    modulus (fst (fromPolar (r , u))) ≡ fst r
  fromPolar-modulus r u =
    cong modulus (fromPolar-value r u) ∙ modulus-scale-unit r u


opaque
  inverse-times-equal : ∀ m r (m# : rat 0 ＃ m) →
    m ≡ r → invℝ m m# ·ᵣ r ≡ 1
  inverse-times-equal m r m# m≡r =
    cong (invℝ m m# ·ᵣ_) (sym m≡r)
    ∙ inverse-times-self m m#


opaque
  fromPolar-modulus-apart : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    rat 0 ＃ modulus (scaleℂ (fst r) (fst u))
  fromPolar-modulus-apart r u = inl (fromPolarModulusPositive r u)


opaque
  fromPolar-coefficient-one : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    invℝ (modulus (scaleℂ (fst r) (fst u)))
      (fromPolar-modulus-apart r u) ·ᵣ fst r ≡ 1
  fromPolar-coefficient-one r u =
    inverse-times-equal
      (modulus (scaleℂ (fst r) (fst u))) (fst r)
      (fromPolar-modulus-apart r u)
      (modulus-scale-unit r u)


opaque
  scale-to-unit-from-path : ∀ z s r (u : UnitCircleℂ) →
    z ≡ scaleℂ r (fst u) → s ·ᵣ r ≡ 1 → scaleℂ s z ≡ fst u
  scale-to-unit-from-path z s r u z≡ru sr≡1 =
    cong (scaleℂ s) z≡ru
    ∙ reconstruct-scaled-inverse s r (fst u) sr≡1


opaque
  directionValue-scaled-unit-from-path :
    ∀ z (z# : 0ℂ #ℂ z) r (u : UnitCircleℂ) →
    z ≡ scaleℂ r (fst u) → modulus z ≡ r →
    directionValue z z# ≡ fst u
  directionValue-scaled-unit-from-path z z# r u z≡ru modulus≡r =
    directionValue-path z z#
    ∙ scale-to-unit-from-path
        z (invℝ (modulus z) (0#modulus z#)) r u z≡ru
        (inverse-times-equal
          (modulus z) r (0#modulus z#) modulus≡r)


opaque
  fromPolar-direction-value : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    directionValue
      (fst (fromPolar (r , u))) (snd (fromPolar (r , u))) ≡ fst u
  fromPolar-direction-value r u =
    directionValue-scaled-unit-from-path
      (fst (fromPolar (r , u))) (snd (fromPolar (r , u)))
      (fst r) u (fromPolar-value r u) (fromPolar-modulus r u)


opaque
  unitDirection-scale-unit : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    unitDirection (fst (fromPolar (r , u))) (snd (fromPolar (r , u))) ≡ u
  unitDirection-scale-unit r u = unitCircleℂ≡
    (unitDirection-value
      (fst (fromPolar (r , u))) (snd (fromPolar (r , u)))
    ∙ fromPolar-direction-value r u)


pair-path : ∀ {A B : Type} {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
pair-path a≡a' b≡b' = cong₂ _,_ a≡a' b≡b'


opaque
  polarCoordinates-path : ∀ z →
    polarCoordinates z ≡
      (polarRadius z , unitDirection (fst z) (snd z))
  polarCoordinates-path z = refl


opaque
  polarRadius-with-positive : ∀ z (0#z : 0ℂ #ℂ z)
    (0<|z| : 0 <ᵣ modulus z) →
    polarRadius (z , 0#z) ≡ (modulus z , 0<|z|)
  polarRadius-with-positive z 0#z 0<|z| = ℝ₊≡ refl


fromPolar-radius-explicit : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
  polarRadius
    (scaleℂ (fst r) (fst u) , fromPolarApart r u) ≡ r
fromPolar-radius-explicit r u =
  polarRadius-with-positive
    (scaleℂ (fst r) (fst u)) (fromPolarApart r u)
    (fromPolarModulusPositive r u)
  ∙ ℝ₊≡ (modulus-scale-unit r u)


opaque
  fromPolar-pair-path : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    fromPolar (r , u) ≡
      (scaleℂ (fst r) (fst u) , fromPolarApart r u)
  fromPolar-pair-path r u = refl


opaque
  fromPolar-radius-projected : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
    polarRadius (fromPolar (r , u)) ≡ r
  fromPolar-radius-projected r u =
    cong polarRadius (fromPolar-pair-path r u)
    ∙ fromPolar-radius-explicit r u


unitDirection-scale-unit-explicit : ∀ (r : ℝ₊) (u : UnitCircleℂ) →
  unitDirection (scaleℂ (fst r) (fst u)) (fromPolarApart r u) ≡ u
unitDirection-scale-unit-explicit r u = unitCircleℂ≡
  (unitDirection-value
    (scaleℂ (fst r) (fst u)) (fromPolarApart r u)
  ∙ directionValue-scaled-unit-from-path
      (scaleℂ (fst r) (fst u)) (fromPolarApart r u)
      (fst r) u refl (modulus-scale-unit r u))


opaque
  Polarℂ≡ : ∀ (p q : Polarℂ) →
    fst p ≡ fst q → snd p ≡ snd q → p ≡ q
  Polarℂ≡ (r , u) (s , v) r≡s u≡v = pair-path r≡s u≡v


polarSec : ∀ p → polarCoordinates (fromPolar p) ≡ p
polarSec (r , u) = Polarℂ≡
  (polarCoordinates (fromPolar (r , u))) (r , u)
  (fromPolar-radius-projected r u)
  (unitDirection-scale-unit r u)

opaque
  polarRet : ∀ z → fromPolar (polarCoordinates z) ≡ z
  polarRet (z , 0#z) = ℂˣ≡ (polarReconstruct z 0#z)

polarIso : Iso ℂˣ Polarℂ
polarIso = iso polarCoordinates fromPolar polarSec polarRet


polarEquiv : ℂˣ ≃ Polarℂ
polarEquiv = isoToEquiv polarIso
