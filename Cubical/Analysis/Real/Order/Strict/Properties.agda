module Cubical.Analysis.Real.Order.Strict.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun; invEq)

open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Relation.Binary.Order.Quoset.Base
  using (IsQuoset; Quoset; quoset)
open import Cubical.Relation.Nullary

open import Cubical.Analysis.Real.Base
  using (ℝ; rat; isSetℝ)
open import Cubical.Analysis.Real.Algebra.Addition
  using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (addIdR; addAssoc)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; isProp≤ℝ; ≤ℝ-trans; rat≤rat≃)
open import Cubical.Analysis.Real.Order.Addition
  using (addPres≤R; addPres≤L; addReflects≤L)
open import Cubical.Analysis.Real.Order.Strict.Base

open ℚInstance.PositiveRationals using (ℚ₊; _+₊_)


private
  combineGapPath : ∀ (x : ℝ) (δ ε : ℚ₊) →
    x + rat (fst (δ +₊ ε)) ≡
    (x + rat (fst δ)) + rat (fst ε)
  combineGapPath x δ ε =
    cong (x +_) (sym (rat+rat (fst δ) (fst ε)))
    ∙ addAssoc x (rat (fst δ)) (rat (fst ε))


<ℝ-trans : ∀ x y z → x <ℝ y → y <ℝ z → x <ℝ z
<ℝ-trans x y z = PT.map2 λ (δ , u≤y) (ε , v≤z) →
  δ +₊ ε ,
    (subst (_≤ℝ z)
      (sym (combineGapPath x δ ε))
      (≤ℝ-trans
        ((x + rat (fst δ)) + rat (fst ε))
        (y + rat (fst ε)) z
        (addPres≤R
          (x + rat (fst δ)) y
          (rat (fst ε)) u≤y)
        v≤z))

≤<ℝ-trans : ∀ x y z → x ≤ℝ y → y <ℝ z → x <ℝ z
≤<ℝ-trans x y z x≤y = PT.map λ (δ , yδ≤z) →
  δ ,
    (≤ℝ-trans
      (x + rat (fst δ))
      (y + rat (fst δ)) z
      (addPres≤R x y (rat (fst δ)) x≤y)
      yδ≤z)

<≤ℝ-trans : ∀ x y z → x <ℝ y → y ≤ℝ z → x <ℝ z
<≤ℝ-trans x y z x<y y≤z = PT.map
  (λ (δ , xδ≤y) → δ ,
    ≤ℝ-trans (x + rat (fst δ)) y z xδ≤y y≤z)
  x<y

<ℝ-weaken : ∀ x y → x <ℝ y → x ≤ℝ y
<ℝ-weaken x y = PT.rec (isProp≤ℝ x y) λ (δ , xδ≤y) →
  ≤ℝ-trans x (x + rat (fst δ)) y
    (subst (_≤ℝ (x + rat (fst δ)))
      (addIdR x)
      (addPres≤L
        (rat 0) (rat (fst δ)) x
        (invEq (rat≤rat≃ 0 (fst δ))
          (ℚOrder.<Weaken≤ 0 (fst δ) (snd δ)))))
    xδ≤y

<ℝ-irrefl : ∀ x → ¬ x <ℝ x
<ℝ-irrefl x = PT.rec isProp⊥ λ (δ , xδ≤x) →
  ℚOrder.isIrrefl< 0
    (ℚOrder.isTrans<≤ 0 (fst δ) 0
      (snd δ) (width≤0 δ xδ≤x))
  where
  width≤0 : ∀ δ → GapBound x x δ → fst δ ℚOrder.≤ 0
  width≤0 δ xδ≤x = equivFun (rat≤rat≃ (fst δ) 0)
    (addReflects≤L
      (rat (fst δ)) (rat 0) x
      (subst ((x + rat (fst δ)) ≤ℝ_)
        (sym (addIdR x)) xδ≤x))

<ℝ-asym : ∀ x y → x <ℝ y → y <ℝ x → ⊥
<ℝ-asym x y x<y y<x =
  <ℝ-irrefl x (<ℝ-trans x y x x<y y<x)

≤ℝ→≯ : ∀ x y → x ≤ℝ y → ¬ y <ℝ x
≤ℝ→≯ x y x≤y y<x =
  <ℝ-irrefl y (<≤ℝ-trans y x y y<x x≤y)

<ℝ→≰ : ∀ x y → x <ℝ y → ¬ y ≤ℝ x
<ℝ→≰ x y x<y y≤x = ≤ℝ→≯ y x y≤x x<y

<ℝ→≢ : ∀ x y → x <ℝ y → ¬ x ≡ y
<ℝ→≢ x y x<y x≡y =
  <ℝ-irrefl y (subst (_<ℝ y) x≡y x<y)


isQuoset<ℝ : IsQuoset _<ℝ_
isQuoset<ℝ .IsQuoset.is-set = isSetℝ
isQuoset<ℝ .IsQuoset.is-prop-valued = isProp<ℝ
isQuoset<ℝ .IsQuoset.is-irrefl = <ℝ-irrefl
isQuoset<ℝ .IsQuoset.is-trans = <ℝ-trans
isQuoset<ℝ .IsQuoset.is-asym = <ℝ-asym

ℝ<Quoset : Quoset ℓ-zero ℓ-zero
ℝ<Quoset = quoset ℝ _<ℝ_ isQuoset<ℝ
