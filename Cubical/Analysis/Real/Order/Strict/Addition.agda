module Cubical.Analysis.Real.Order.Strict.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addComm; addIdR; addIdL; addAssoc)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
  using (_-_; addInvR; addInvL; subSelf; negInvol)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Addition
  using (addPres≤R; addPres≤L)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-trans; ≤<ℝ-trans; <≤ℝ-trans)


private
  translateGapRPath : ∀ x z q →
    (x + z) + rat q ≡ (x + rat q) + z
  translateGapRPath x z q =
    sym (addAssoc x z (rat q))
    ∙ cong (x +_) (addComm z (rat q))
    ∙ addAssoc x (rat q) z

  addCancelRPath : ∀ x z → (x + z) + (- z) ≡ x
  addCancelRPath x z =
    sym (addAssoc x z (- z))
    ∙ cong (x +_) (addInvR z)
    ∙ addIdR x

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


<ℝ-addR : ∀ x y z → x <ℝ y → x + z <ℝ y + z
<ℝ-addR x y z = PT.map λ (δ , xδ≤y) →
  δ ,
    (subst (_≤ℝ (y + z))
      (sym (translateGapRPath x z (fst δ)))
      (addPres≤R
        (x + rat (fst δ)) y z xδ≤y))

<ℝ-addL : ∀ x y z → x <ℝ y → z + x <ℝ z + y
<ℝ-addL x y z =
  subst2 _<ℝ_ (addComm x z) (addComm y z)
  ∘ <ℝ-addR x y z

<ℝ-add : ∀ x y z w →
  x <ℝ y → z <ℝ w → x + z <ℝ y + w
<ℝ-add x y z w x<y z<w =
  <ℝ-trans (x + z) (y + z) (y + w)
    (<ℝ-addR x y z x<y)
    (<ℝ-addL z w y z<w)

≤<ℝ-add : ∀ x y z w →
  x ≤ℝ y → z <ℝ w → x + z <ℝ y + w
≤<ℝ-add x y z w x≤y z<w =
  ≤<ℝ-trans (x + z) (y + z) (y + w)
    (addPres≤R x y z x≤y)
    (<ℝ-addL z w y z<w)

<≤ℝ-add : ∀ x y z w →
  x <ℝ y → z ≤ℝ w → x + z <ℝ y + w
<≤ℝ-add x y z w x<y z≤w =
  <≤ℝ-trans (x + z) (y + z) (y + w)
    (<ℝ-addR x y z x<y)
    (addPres≤L z w y z≤w)

<ℝ-addR-cancel : ∀ x y z → x + z <ℝ y + z → x <ℝ y
<ℝ-addR-cancel x y z =
  subst2 _<ℝ_ (addCancelRPath x z) (addCancelRPath y z)
  ∘ <ℝ-addR (x + z) (y + z) (- z)

<ℝ-addL-cancel : ∀ x y z → z + x <ℝ z + y → x <ℝ y
<ℝ-addL-cancel x y z =
  <ℝ-addR-cancel x y z
  ∘ subst2 _<ℝ_ (addComm z x) (addComm z y)

addR<Equiv : ∀ x y z → (x + z <ℝ y + z) ≃ (x <ℝ y)
addR<Equiv x y z = propBiimpl→Equiv
  (isProp<ℝ (x + z) (y + z)) (isProp<ℝ x y)
  (<ℝ-addR-cancel x y z) (<ℝ-addR x y z)

positiveSub : ∀ x y → x <ℝ y → 0ℝ <ℝ y - x
positiveSub x y x<y = subst2 _<ℝ_
  (subSelf x) refl (<ℝ-addR x y (- x) x<y)

positiveSub→< : ∀ x y → 0ℝ <ℝ y - x → x <ℝ y
positiveSub→< x y 0<y-x = subst2 _<ℝ_
  (addIdL x) (subAddCancel y x)
  (<ℝ-addR 0ℝ (y - x) x 0<y-x)

<ℝ-neg : ∀ x y → x <ℝ y → (- y) <ℝ (- x)
<ℝ-neg x y x<y = subst2 _<ℝ_
  (addAssoc x (- x) (- y)
    ∙ cong (_+ (- y)) (addInvR x)
    ∙ addIdL (- y))
  (cong (y +_) (addComm (- x) (- y))
    ∙ addAssoc y (- y) (- x)
    ∙ cong (_+ (- x)) (addInvR y)
    ∙ addIdL (- x))
  (<ℝ-addR x y ((- x) + (- y)) x<y)

neg<ℝ : ∀ x y → (- y) <ℝ (- x) → x <ℝ y
neg<ℝ x y = subst2 _<ℝ_ (negInvol x) (negInvol y)
  ∘ <ℝ-neg (- y) (- x)
