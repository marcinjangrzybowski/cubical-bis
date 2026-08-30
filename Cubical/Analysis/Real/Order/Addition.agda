module Cubical.Analysis.Real.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures


private
  composeContinuous :
    (f g : ℝ → ℝ) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) (f ∘ g) (ℝPremetricSpace .snd)
  composeContinuous f g f-cont g-cont =
    snd ((f , f-cont) ∘C (g , g-cont))

  constant-isContinuous : ∀ c → isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
  constant-isContinuous c = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ ε _ → refl∼ c ε


addMax : ∀ x y z →
  maxℝ x y + z ≡ maxℝ (x + z) (y + z)
addMax = continuousExtensionality₃
  (λ x y z → maxℝ x y + z)
  (λ x y z → maxℝ (x + z) (y + z))
  (λ y z → composeContinuous
    (_+ z) (λ x → maxℝ x y)
    (add-isContinuous₁ z) (max-isContinuous₁ y))
  (λ x z → composeContinuous
    (_+ z) (maxℝ x)
    (add-isContinuous₁ z) (max-isContinuous₂ x))
  (λ x y → add-isContinuous₂ (maxℝ x y))
  (λ y z → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (_+ z) (λ _ → y + z)
    (add-isContinuous₁ z) (constant-isContinuous (y + z)))
  (λ x z → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (λ _ → x + z) (_+ z)
    (constant-isContinuous (x + z)) (add-isContinuous₁ z))
  (λ x y → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (x +_) (y +_)
    (add-isContinuous₂ x) (add-isContinuous₂ y))
  λ p q r →
    cong (_+ rat r) (max-rat p q)
    ∙ rat+rat (ℚ.max p q) r
    ∙ cong rat (ℚ.+MaxDistrℚ p q r)
    ∙ sym (max-rat (p ℚ.+ r) (q ℚ.+ r))
    ∙ cong₂ maxℝ (sym (rat+rat p r)) (sym (rat+rat q r))

addPres≤R : ∀ x y z → x ≤ℝ y → x + z ≤ℝ y + z
addPres≤R x y z x≤y =
  sym (addMax x y z)
  ∙ cong (_+ z) x≤y

addPres≤L : ∀ x y z → x ≤ℝ y → z + x ≤ℝ z + y
addPres≤L x y z x≤y = subst2 _≤ℝ_
  (addComm x z) (addComm y z)
  (addPres≤R x y z x≤y)

private
  addCancelRPath : ∀ x z → (x + z) + (- z) ≡ x
  addCancelRPath x z =
    sym (addAssoc x z (- z))
    ∙ cong (x +_) (addInvR z)
    ∙ addIdR x


addReflects≤R : ∀ x y z → x + z ≤ℝ y + z → x ≤ℝ y
addReflects≤R x y z translated = subst2 _≤ℝ_
  (addCancelRPath x z) (addCancelRPath y z)
  (addPres≤R (x + z) (y + z) (- z) translated)

addReflects≤L : ∀ x y z → z + x ≤ℝ z + y → x ≤ℝ y
addReflects≤L x y z translated =
  addReflects≤R x y z
    (subst2 _≤ℝ_ (addComm z x) (addComm z y) translated)

negPres≤ : ∀ x y → x ≤ℝ y → (- y) ≤ℝ (- x)
negPres≤ x y x≤y =
  sym (negInvol (maxℝ (- y) (- x)))
  ∙ cong -_ minYX
  where
  minXY : minℝ x y ≡ x
  minXY =
    sym (cong (minℝ x) x≤y)
    ∙ minAbsorbMax x y

  minYX : minℝ y x ≡ x
  minYX = minComm y x ∙ minXY

negReflects≤ : ∀ x y → (- y) ≤ℝ (- x) → x ≤ℝ y
negReflects≤ x y negY≤negX =
  subst2 _≤ℝ_ (negInvol x) (negInvol y)
    (negPres≤ (- y) (- x) negY≤negX)
