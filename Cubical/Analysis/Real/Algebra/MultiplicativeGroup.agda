module Cubical.Analysis.Real.Algebra.MultiplicativeGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order


-- Positive reals form a multiplicative abelian group. This construction uses
-- only real arithmetic and reciprocal laws, not exponential or logarithm.
opaque
  1>0 : ℝ>0
  1>0 = positiveRat 1₊

  1>0-value : fst 1>0 ≡ 1ℝ
  1>0-value = refl


opaque
  positiveInverse : ℝ>0 → ℝ>0
  positiveInverse value =
    positiveReciprocal (fst value) (snd value)
    , positiveReciprocalPositive (fst value) (snd value)

  positiveInverse-value : ∀ value →
    fst (positiveInverse value) ≡ positiveReciprocal (fst value) (snd value)
  positiveInverse-value value = refl


opaque
  positiveMulAssoc : ∀ x y z →
    x ·>0 (y ·>0 z) ≡ (x ·>0 y) ·>0 z
  positiveMulAssoc x y z =
    Σ≡Prop isPropIsPositive (mulAssoc (fst x) (fst y) (fst z))

  positiveMulComm : ∀ x y → x ·>0 y ≡ y ·>0 x
  positiveMulComm x y = Σ≡Prop isPropIsPositive (mulComm (fst x) (fst y))

  positiveMulIdR : ∀ x → x ·>0 1>0 ≡ x
  positiveMulIdR x = Σ≡Prop isPropIsPositive
    (cong (fst x ·_) 1>0-value ∙ mulIdR (fst x))

  positiveMulIdL : ∀ x → 1>0 ·>0 x ≡ x
  positiveMulIdL x = positiveMulComm 1>0 x ∙ positiveMulIdR x

  positiveMulInvR : ∀ x → x ·>0 positiveInverse x ≡ 1>0
  positiveMulInvR x = Σ≡Prop isPropIsPositive
    (cong (fst x ·_) (positiveInverse-value x)
    ∙ positiveReciprocalLaw (fst x) (snd x) ∙ sym 1>0-value)

  positiveMulInvL : ∀ x → positiveInverse x ·>0 x ≡ 1>0
  positiveMulInvL x = positiveMulComm (positiveInverse x) x ∙ positiveMulInvR x


ℝ>0AbGroup : AbGroup ℓ-zero
ℝ>0AbGroup = makeAbGroup 1>0 _·>0_ positiveInverse isSetℝ>0
  positiveMulAssoc positiveMulIdR positiveMulInvR positiveMulComm


ℝ>0Group : Group ℓ-zero
ℝ>0Group = AbGroup→Group ℝ>0AbGroup


opaque
  positiveInverseInvol : ∀ x → positiveInverse (positiveInverse x) ≡ x
  positiveInverseInvol x = GroupTheory.invInv ℝ>0Group x

  positiveInverseOne : positiveInverse 1>0 ≡ 1>0
  positiveInverseOne = GroupTheory.inv1g ℝ>0Group

infixl 7 _/>0_

_/>0_ : ℝ>0 → ℝ>0 → ℝ>0
x />0 y = x ·>0 positiveInverse y

opaque
  positiveDivSelf : ∀ x → x />0 x ≡ 1>0
  positiveDivSelf = positiveMulInvR

  positiveDivOne : ∀ x → x />0 1>0 ≡ x
  positiveDivOne x = cong (x ·>0_) positiveInverseOne ∙ positiveMulIdR x
