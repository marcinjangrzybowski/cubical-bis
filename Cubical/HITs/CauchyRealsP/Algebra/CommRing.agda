module Cubical.HITs.CauchyRealsP.Algebra.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Associativity
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Distributivity

ℝCommRing : CommRing ℓ-zero
ℝCommRing =
  makeCommRing
    0 1 _+_ _·_ -_
    isSetℝ
    addAssoc addIdR addInvR addComm
    (λ x y z → sym (mulAssoc x y z))
    mulIdR mulDistR mulComm

ratIsCommRingHom :
  IsCommRingHom (snd ℚCommRing) rat (snd ℝCommRing)
ratIsCommRingHom =
  makeIsCommRingHom
    refl
    (λ q r → sym (rat+rat q r))
    (λ q r → sym (mul-rat q r))

ratCommRingHom : CommRingHom ℚCommRing ℝCommRing
ratCommRingHom = rat , ratIsCommRingHom
