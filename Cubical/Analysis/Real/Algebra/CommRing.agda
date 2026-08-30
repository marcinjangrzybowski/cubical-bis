module Cubical.Analysis.Real.Algebra.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws


ℝCommRing : CommRing ℓ-zero
ℝCommRing = makeCommRing
  0ℝ 1ℝ _+_ _·_ -_
  isSetℝ
  addAssoc addIdR addInvR addComm
  mulAssoc mulIdR mulDistR mulComm

ratIsCommRingHom :
  IsCommRingHom (ℚCommRing .snd) rat (ℝCommRing .snd)
ratIsCommRingHom = makeIsCommRingHom
  refl
  (λ p q → sym (rat+rat p q))
  (λ p q → sym (mul-rat p q))

ratCommRingHom : CommRingHom ℚCommRing ℝCommRing
ratCommRingHom = rat , ratIsCommRingHom
