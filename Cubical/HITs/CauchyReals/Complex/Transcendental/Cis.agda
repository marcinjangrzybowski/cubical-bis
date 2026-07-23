module Cubical.HITs.CauchyReals.Complex.Transcendental.Cis where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  (sin; cos; sin0=0; cos0=1; sin-odd; cos-even
  ; sin·sin+cos·cos=1)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using
  (sinOfSum; cosOfSum)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.UnitCircle

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


cis : ℝ → ℂ
cis x = cos x , sin x


cisUnit : ℝ → UnitCircleℂ
cisUnit x = cis x , +ᵣComm _ _ ∙ sin·sin+cos·cos=1 x


opaque
  cis0 : cis 0 ≡ 1ℂ
  cis0 = ℂ≡ cos0=1 sin0=0


opaque
  cis-add : ∀ x y → cis (x +ᵣ y) ≡ cis x ·ℂ cis y
  cis-add x y = ℂ≡ (cosOfSum x y) (sinOfSum x y ∙ ℝ!)


opaque
  cis-neg : ∀ x → cis (-ᵣ x) ≡ conj (cis x)
  cis-neg x = ℂ≡ (sym (cos-even x)) (sym (sin-odd x))


opaque
  cis-modulus : ∀ x → modulus (cis x) ≡ 1
  cis-modulus x = normSqOne→modulusOne (cis x) (snd (cisUnit x))
