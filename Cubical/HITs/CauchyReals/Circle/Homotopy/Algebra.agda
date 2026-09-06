module Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos; isSetℤ)
open import Cubical.Data.Rationals using ([_/_])
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Additivity
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)

circle-image-injective : ∀ x y → Circle→distCircle x ≡ Circle→distCircle y → x ≡ y
circle-image-injective x y p = invEq (congEquiv cartesianEquivalence)
  (cartesianEquivalence-β x ∙ p ∙ sym (cartesianEquivalence-β y))

maps-by-image : (f g : CircleMap) →
  (∀ x → Circle→distCircle (fst f x) ≡ Circle→distCircle (fst g x)) → f ≡ g
maps-by-image f g p = Σ≡Prop (λ _ → squash₁)
  (funExt (λ x → circle-image-injective (fst f x) (fst g x) (p x)))

zeroCircleMap : CircleMap
zeroCircleMap = constantUC (injCircle 0)

private
  image-zero : ∀ x → Circle→distCircle (fst zeroCircleMap x) ≡ circle0
  image-zero x = injCircle0≡circle0

  add-assoc : (f g h : CircleMap) →
    addCircleUC f (addCircleUC g h) ≡ addCircleUC (addCircleUC f g) h
  add-assoc f g h = maps-by-image _ _ λ x →
    addCircle-image f (addCircleUC g h) x
    ∙ cong (Circle→distCircle (fst f x) ℝS¹.+_) (addCircle-image g h x)
    ∙ ℝS¹.+Assoc _ _ _
    ∙ cong (ℝS¹._+ Circle→distCircle (fst h x)) (sym (addCircle-image f g x))
    ∙ sym (addCircle-image (addCircleUC f g) h x)

  add-zero : (f : CircleMap) → addCircleUC f zeroCircleMap ≡ f
  add-zero f = maps-by-image _ _ λ x → addCircle-image f zeroCircleMap x
    ∙ cong (Circle→distCircle (fst f x) ℝS¹.+_) (image-zero x) ∙ ℝS¹.+IdR _

  add-neg : (f : CircleMap) → addCircleUC f (negCircleUC f) ≡ zeroCircleMap
  add-neg f = maps-by-image _ _ λ x → addCircle-image f (negCircleUC f) x
    ∙ cong (Circle→distCircle (fst f x) ℝS¹.+_) (negCircle-image f x)
    ∙ ℝS¹.+InvR _ ∙ sym (image-zero x)

  add-comm : (f g : CircleMap) → addCircleUC f g ≡ addCircleUC g f
  add-comm f g = maps-by-image _ _ λ x → addCircle-image f g x
    ∙ ℝS¹.+Comm _ _ ∙ sym (addCircle-image g f x)

CircleMapAbGroup : AbGroup ℓ-zero
CircleMapAbGroup = makeAbGroup zeroCircleMap addCircleUC negCircleUC
  (isSetΣSndProp (isSet→ isSetCircle) (λ _ → squash₁))
  add-assoc add-zero add-neg add-comm

IntegerAbGroup : AbGroup ℓ-zero
IntegerAbGroup = makeAbGroup 0 ℤ._+_ ℤ.-_ isSetℤ ℤ.+Assoc ℤ.+IdR ℤ.-Cancel ℤ.+Comm

private
  loopOf : CircleMap → UC[ ℝPremetricSpace , distCirclePremetricSpace ]
  loopOf f = Circle→distCircleUC ∘UC (f ∘UC injCircleUC)
  loop-closes : ∀ f → fst (loopOf f) 0 ≡ fst (loopOf f) 1
  loop-closes f = cong (Circle→distCircle ∘ fst f) (eq/ 0 1 (-1 , -ᵣ-rat₂ 0 1))

windingNumber-add : (f g : CircleMap) →
  windingNumber (addCircleUC f g) ≡ windingNumber f ℤ.+ windingNumber g
windingNumber-add f g =
  windingLoop-cong (loopOf (addCircleUC f g)) summed (loop-closes (addCircleUC f g))
    (cong₂ ℝS¹._+_ (loop-closes f) (loop-closes g))
    (λ x → addCircle-image f g (injCircle x))
  ∙ windingLoop-add (loopOf f) (loopOf g) (snd summed) (loop-closes f) (loop-closes g)
  where
  summed : UC[ ℝPremetricSpace , distCirclePremetricSpace ]
  summed = addDistCircleUC (loopOf f) (loopOf g)

windingHom : AbGroupHom CircleMapAbGroup IntegerAbGroup
windingHom = windingNumber , makeIsGroupHom windingNumber-add
