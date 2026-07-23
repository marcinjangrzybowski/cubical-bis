module Cubical.HITs.CauchyReals.Complex.UnitCircle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.AbGroup

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using
  (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws

open import Cubical.HITs.CauchyReals.Circle.Base using
  (distCircle)
open import Cubical.HITs.CauchyReals.Circle.Core using
  (Circle)
open import Cubical.HITs.CauchyReals.Circle.Equivalence using
  (Circle≃distCircle)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


UnitCircleℂ : Type
UnitCircleℂ = Σ[ z ∈ ℂ ] normSq z ≡ 1


UnitModulusℂ : Type
UnitModulusℂ = Σ[ z ∈ ℂ ] modulus z ≡ 1


unitCircleℂ≡ : ∀ {z w : UnitCircleℂ} → fst z ≡ fst w → z ≡ w
unitCircleℂ≡ = Σ≡Prop (λ _ → isSetℝ _ _)


unitModulusℂ≡ : ∀ {z w : UnitModulusℂ} → fst z ≡ fst w → z ≡ w
unitModulusℂ≡ = Σ≡Prop (λ _ → isSetℝ _ _)


isSetUnitCircleℂ : isSet UnitCircleℂ
isSetUnitCircleℂ = isSetΣ isSetℂ (λ _ → isProp→isSet (isSetℝ _ _))


isSetUnitModulusℂ : isSet UnitModulusℂ
isSetUnitModulusℂ = isSetΣ isSetℂ (λ _ → isProp→isSet (isSetℝ _ _))


normSqOne→modulusOne : ∀ z → normSq z ≡ 1 → modulus z ≡ 1
normSqOne→modulusOne z norm≡1 =
  modulusOfNormSqSquare z 1 (norm≡1 ∙ ℝ!)
  ∙ absᵣPos 1 decℚ<ᵣ?


modulusOne→normSqOne : ∀ z → modulus z ≡ 1 → normSq z ≡ 1
modulusOne→normSqOne z |z|≡1 =
  sym (modulusSq z)
  ∙ cong₂ _·ᵣ_ |z|≡1 |z|≡1
  ∙ ℝ!


unitCircle→unitModulus : UnitCircleℂ → UnitModulusℂ
unitCircle→unitModulus (z , norm≡1) = z , normSqOne→modulusOne z norm≡1


unitModulus→unitCircle : UnitModulusℂ → UnitCircleℂ
unitModulus→unitCircle (z , |z|≡1) = z , modulusOne→normSqOne z |z|≡1


UnitCircle≃UnitModulus : UnitCircleℂ ≃ UnitModulusℂ
UnitCircle≃UnitModulus = isoToEquiv unitCircleUnitModulusIso
  where
  unitCircleUnitModulusIso : Iso UnitCircleℂ UnitModulusℂ
  unitCircleUnitModulusIso .Iso.fun = unitCircle→unitModulus
  unitCircleUnitModulusIso .Iso.inv = unitModulus→unitCircle
  unitCircleUnitModulusIso .Iso.sec _ = unitModulusℂ≡ refl
  unitCircleUnitModulusIso .Iso.ret _ = unitCircleℂ≡ refl


1UnitCircleℂ : UnitCircleℂ
1UnitCircleℂ = 1ℂ , normSq1


_·S¹_ : UnitCircleℂ → UnitCircleℂ → UnitCircleℂ
(z , normz) ·S¹ (w , normw) = z ·ℂ w ,
  normSq-mul z w ∙ cong₂ _·ᵣ_ normz normw ∙ ℝ!


invS¹ : UnitCircleℂ → UnitCircleℂ
invS¹ (z , normz) = conj z , normSq-conj z ∙ normz


UnitCircleℂAbGroup : AbGroup ℓ-zero
UnitCircleℂAbGroup = makeAbGroup
  1UnitCircleℂ _·S¹_ invS¹
  isSetUnitCircleℂ
  (λ x y z → unitCircleℂ≡ (·ℂAssoc (fst x) (fst y) (fst z)))
  (λ z → unitCircleℂ≡ (·ℂIdR (fst z)))
  (λ z → unitCircleℂ≡
    (mul-conj (fst z) ∙ cong fromℝ (snd z)))
  (λ z w → unitCircleℂ≡ (·ℂComm (fst z) (fst w)))


UnitCircleℂ≃distCircle : UnitCircleℂ ≃ distCircle
UnitCircleℂ≃distCircle = isoToEquiv unitCircleDistCircleIso
  where
  unitCircleDistCircleIso : Iso UnitCircleℂ distCircle
  unitCircleDistCircleIso .Iso.fun (z , p) = z , p
  unitCircleDistCircleIso .Iso.inv (z , p) = z , p
  unitCircleDistCircleIso .Iso.sec _ = refl
  unitCircleDistCircleIso .Iso.ret _ = refl


Circle≃UnitCircleℂ : Circle ≃ UnitCircleℂ
Circle≃UnitCircleℂ = Circle≃distCircle ∙ₑ invEquiv UnitCircleℂ≃distCircle
