module Cubical.Analysis.Real.Order.Strict.Rational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; ≤ℝ-refl; rat≤rat≃)
open import Cubical.Analysis.Real.Order.Strict.Base

open ℚInstance.PositiveRationals using (ℚ₊)


<ℚ→<ℝ : ∀ p q → p ℚOrder.< q → rat p <ℝ rat q
<ℚ→<ℝ p q p<q =
  ∣ positiveGap {x = rat p} {y = rat q} δ rationalBound ∣₁
  where
  δ : ℚ₊
  δ = q ℚ.- p ,
    subst2 ℚOrder._<_ (ℚ.+InvR p) refl
      (ℚOrder.<-+o p q (ℚ.- p) p<q)

  gapPath : rat p + rat (fst δ) ≡ rat q
  gapPath =
    rat+rat p (q ℚ.- p)
    ∙ cong rat
        (ℚ.+Comm p (q ℚ.- p)
        ∙ sym (ℚ.+Assoc q (ℚ.- p) p)
        ∙ cong (q ℚ.+_) (ℚ.+InvL p)
        ∙ ℚ.+IdR q)

  rationalBound : GapBound (rat p) (rat q) δ
  rationalBound = subst (λ z → z ≤ℝ rat q)
    (sym gapPath) (≤ℝ-refl (rat q))

<ℝ→<ℚ : ∀ p q → rat p <ℝ rat q → p ℚOrder.< q
<ℝ→<ℚ p q = PT.rec (ℚOrder.isProp< p q) fromGap
  where
  fromGap : PositiveGap (rat p) (rat q) → p ℚOrder.< q
  fromGap (δ , gap) = ℚOrder.isTrans<≤
    p (p ℚ.+ fst δ) q
    (subst2 ℚOrder._<_ (ℚ.+IdR p) refl
      (ℚOrder.<-o+ 0 (fst δ) p (snd δ)))
    rationalBound
    where
    rationalBound : p ℚ.+ fst δ ℚOrder.≤ q
    rationalBound = equivFun
      (rat≤rat≃ (p ℚ.+ fst δ) q)
      (subst (λ z → z ≤ℝ rat q)
        (rat+rat p (fst δ))
        gap)

rat<rat≃ : ∀ p q → (rat p <ℝ rat q) ≃ (p ℚOrder.< q)
rat<rat≃ p q = propBiimpl→Equiv
  (isProp<ℝ (rat p) (rat q)) (ℚOrder.isProp< p q)
  (<ℝ→<ℚ p q) (<ℚ→<ℝ p q)
