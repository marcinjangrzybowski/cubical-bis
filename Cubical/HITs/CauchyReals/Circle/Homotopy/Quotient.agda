module Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ; isSetℤ)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Binary.Base
open CategoryStructures using (_∘UC_)

homotopy-refl : (f : CircleMap) → UniformHomotopy f f
homotopy-refl f = (f ∘UC productSndUC) , (λ _ → refl) , (λ _ → refl)

homotopy-add : (f f' g g' : CircleMap) → UniformHomotopy f f' → UniformHomotopy g g' →
  UniformHomotopy (addCircleUC f g) (addCircleUC f' g')
homotopy-add f f' g g' h k = addCircleUC (fst h) (fst k) ,
  (λ x → cong₂ sum (fst (snd h) x) (fst (snd k) x)) ,
  (λ x → cong₂ sum (snd (snd h) x) (snd (snd k) x))
  where
  sum : Circle → Circle → Circle
  sum p q = fromCartesian (Circle→distCircle p ℝS¹.+ Circle→distCircle q)

homotopy-neg : (f g : CircleMap) → UniformHomotopy f g →
  UniformHomotopy (negCircleUC f) (negCircleUC g)
homotopy-neg f g h = negCircleUC (fst h) ,
  (λ x → cong neg (fst (snd h) x)) , (λ x → cong neg (snd (snd h) x))
  where
  neg : Circle → Circle
  neg p = fromCartesian (ℝS¹.- Circle→distCircle p)

Homotopic : CircleMap → CircleMap → Type
Homotopic f g = ∥ UniformHomotopy f g ∥₁

private
  module M = AbGroupStr (snd CircleMapAbGroup)

  cancel-last : ∀ f g → (f M.+ g) M.+ (M.- g) ≡ f
  cancel-last f g = sym (M.+Assoc f g (M.- g)) ∙ cong (f M.+_) (M.+InvR g) ∙ M.+IdR f
  cancel-first : ∀ f g → (f M.+ g) M.+ (M.- f) ≡ g
  cancel-first f g = cong (M._+ (M.- f)) (M.+Comm f g) ∙ cancel-last g f

homotopy-sym : (f g : CircleMap) → UniformHomotopy f g → UniformHomotopy g f
homotopy-sym f g h = subst2 UniformHomotopy (cancel-first f g) (cancel-last f g)
  (homotopy-add (f M.+ g) (f M.+ g) (M.- f) (M.- g)
    (homotopy-refl (f M.+ g)) (homotopy-neg f g h))

homotopy-trans : (f g h : CircleMap) → UniformHomotopy f g → UniformHomotopy g h → UniformHomotopy f h
homotopy-trans f g h p q = subst2 UniformHomotopy (cancel-last f g) (cancel-first g h)
  (homotopy-add (f M.+ g) (g M.+ h) (M.- g) (M.- g)
    (homotopy-add f g g h p q) (homotopy-refl (M.- g)))

homotopic-equivalence : BinaryRelation.isEquivRel Homotopic
BinaryRelation.isEquivRel.reflexive homotopic-equivalence f = ∣ homotopy-refl f ∣₁
BinaryRelation.isEquivRel.symmetric homotopic-equivalence f g = PT.map (homotopy-sym f g)
BinaryRelation.isEquivRel.transitive homotopic-equivalence f g h = PT.map2 (homotopy-trans f g h)

-- Quotienting by actual real-parameter homotopies, independently of winding.
CircleHomotopyClasses : Type
CircleHomotopyClasses = CircleMap SQ./ Homotopic

class : CircleMap → CircleHomotopyClasses
class = SQ.[_]

class-effective : (f g : CircleMap) → class f ≡ class g → Homotopic f g
class-effective = SQ.effective (λ _ _ → squash₁) homotopic-equivalence

private
  add-respects-left : ∀ f f' g → Homotopic f f' → class (addCircleUC f g) ≡ class (addCircleUC f' g)
  add-respects-left f f' g h = SQ.eq/ _ _ (PT.map
    (λ h → homotopy-add f f' g g h (homotopy-refl g)) h)
  add-respects-right : ∀ f g g' → Homotopic g g' → class (addCircleUC f g) ≡ class (addCircleUC f g')
  add-respects-right f g g' h = SQ.eq/ _ _ (PT.map
    (λ h → homotopy-add f f g g' (homotopy-refl f) h) h)

addClass : CircleHomotopyClasses → CircleHomotopyClasses → CircleHomotopyClasses
addClass = SQ.rec2 SQ.squash/ (λ f g → class (addCircleUC f g)) add-respects-left add-respects-right

negClass : CircleHomotopyClasses → CircleHomotopyClasses
negClass = SQ.rec SQ.squash/ (λ f → class (negCircleUC f))
  (λ f g h → SQ.eq/ _ _ (PT.map (homotopy-neg f g) h))

CircleHomotopyAbGroup : AbGroup ℓ-zero
CircleHomotopyAbGroup = makeAbGroup (class zeroCircleMap) addClass negClass SQ.squash/
  (SQ.elimProp3 (λ _ _ _ → SQ.squash/ _ _) λ f g h →
    cong class (AbGroupStr.+Assoc (snd CircleMapAbGroup) f g h))
  (SQ.elimProp (λ _ → SQ.squash/ _ _) λ f → cong class (AbGroupStr.+IdR (snd CircleMapAbGroup) f))
  (SQ.elimProp (λ _ → SQ.squash/ _ _) λ f → cong class (AbGroupStr.+InvR (snd CircleMapAbGroup) f))
  (SQ.elimProp2 (λ _ _ → SQ.squash/ _ _) λ f g → cong class (AbGroupStr.+Comm (snd CircleMapAbGroup) f g))

classHom : AbGroupHom CircleMapAbGroup CircleHomotopyAbGroup
classHom = class , makeIsGroupHom (λ _ _ → refl)

classWinding : CircleHomotopyClasses → ℤ
classWinding = SQ.rec isSetℤ windingNumber
  (λ f g h → PT.rec (isSetℤ _ _) (windingNumber-homotopy f g) h)

classWindingHom : AbGroupHom CircleHomotopyAbGroup IntegerAbGroup
classWindingHom = classWinding , makeIsGroupHom
  (SQ.elimProp2 (λ _ _ → isSetℤ _ _) windingNumber-add)
