module Cubical.Analysis.Circle.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)
open import Cubical.Relation.Binary.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group

-- Turns, formed from the sequential reals themselves.  No comparison with
-- the HIT Cauchy reals, trigonometric inverse, or choice principle is used.
circle-rel : ℝ → ℝ → Type
circle-rel x y = Σ[ k ∈ ℤ ] x - y ≡ integer k

isPropCircle-rel : ∀ x y → isProp (circle-rel x y)
isPropCircle-rel x y (k , p) (l , q) =
  Σ≡Prop (λ _ → isSetℝ _ _) (integer-injective (sym p ∙ q))

private
  difference-chain : ∀ x y z → (x - y) + (y - z) ≡ x - z
  difference-chain x y z =
    addAssoc (x - y) y (- z) ∙ cong (_+ (- z)) (subAddCancel x y)

isEquivRelCircle-rel : BinaryRelation.isEquivRel circle-rel
isEquivRelCircle-rel .BinaryRelation.isEquivRel.reflexive x = ℤ.pos 0 , subSelf x
isEquivRelCircle-rel .BinaryRelation.isEquivRel.symmetric x y (k , p) =
  ℤ.- k , (sym (negSub x y) ∙ cong -_ p ∙ integer-neg k)
isEquivRelCircle-rel .BinaryRelation.isEquivRel.transitive x y z (k , p) (l , q) =
  k ℤ.+ l , (sym (difference-chain x y z) ∙ cong₂ _+_ p q ∙ integer-add k l)

Circle : Type
Circle = ℝ / circle-rel

isSetCircle : isSet Circle
isSetCircle = squash/

cover : ℝ → Circle
cover = [_]

cover-effective : ∀ x y → cover x ≡ cover y → circle-rel x y
cover-effective = SQ.effective isPropCircle-rel isEquivRelCircle-rel

cover-respects : ∀ x y → circle-rel x y → cover x ≡ cover y
cover-respects = eq/

circle0 : Circle
circle0 = cover 0ℝ

private
  add-respects : ∀ a b c d → circle-rel a c → circle-rel b d →
    circle-rel (a + b) (c + d)
  add-respects a b c d (k , p) (l , q) =
    k ℤ.+ l , (differenceOfSums a b c d ∙ cong₂ _+_ p q ∙ integer-add k l)

infixl 6 _+ᶜ_
_+ᶜ_ : Circle → Circle → Circle
_+ᶜ_ = SQ.rec2 isSetCircle (λ x y → cover (x + y))
  (λ a b c r → eq/ _ _
    (add-respects a c b c r (ℤ.pos 0 , subSelf c)))
  (λ a b c r → eq/ _ _
    (add-respects a b a c (ℤ.pos 0 , subSelf a) r))

negCircle : Circle → Circle
negCircle = SQ.rec isSetCircle (λ x → cover (- x))
  (λ a b (k , p) → eq/ _ _
    (ℤ.- k , (differenceOfNegatives a b ∙ cong -_ p ∙ integer-neg k)))

cover-add : ∀ x y → cover (x + y) ≡ cover x +ᶜ cover y
cover-add x y = refl

circle-add-assoc : ∀ p q r → p +ᶜ (q +ᶜ r) ≡ (p +ᶜ q) +ᶜ r
circle-add-assoc = SQ.elimProp3 (λ _ _ _ → isSetCircle _ _)
  (λ x y z → cong cover (addAssoc x y z))

circle-add-zero : ∀ p → p +ᶜ circle0 ≡ p
circle-add-zero = SQ.elimProp (λ _ → isSetCircle _ _) (λ x → cong cover (addIdR x))

circle-add-inverse : ∀ p → p +ᶜ negCircle p ≡ circle0
circle-add-inverse = SQ.elimProp (λ _ → isSetCircle _ _) (λ x → cong cover (addInvR x))

circle-add-comm : ∀ p q → p +ᶜ q ≡ q +ᶜ p
circle-add-comm = SQ.elimProp2 (λ _ _ → isSetCircle _ _)
  (λ x y → cong cover (addComm x y))

CircleAbGroup : AbGroup ℓ-zero
CircleAbGroup = makeAbGroup circle0 _+ᶜ_ negCircle isSetCircle
  circle-add-assoc circle-add-zero circle-add-inverse circle-add-comm

module CircleGroup = GroupTheory (AbGroup→Group CircleAbGroup)

cover-integer : ∀ k → cover (integer k) ≡ circle0
cover-integer k = cover-respects _ _ (k , subZero (integer k))

cover-kernel : ∀ t → cover t ≡ circle0 → Σ[ k ∈ ℤ ] t ≡ integer k
cover-kernel t p = fst witness , sym (subZero t) ∙ snd witness
  where witness = cover-effective t 0ℝ p
