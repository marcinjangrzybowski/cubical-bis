module Cubical.Analysis.Real.Order.Strict.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Algebra.CommRing.Base using (CommRing→Ring)
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication
  using (_·_; mul-rat)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
  using (mulComm)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; rat≤rat≃)
open import Cubical.Analysis.Real.Order.Multiplication
  using (mulPres≤)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-trans; <ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Addition
  using (positiveSub; positiveSub→<)

open ℚInstance.PositiveRationals using (_·₊_)

private module ℝRing = RingProperties.RingTheory (CommRing→Ring ℝCommRing)


mulPositive : ∀ x y → 0ℝ <ℝ x → 0ℝ <ℝ y → 0ℝ <ℝ x · y
mulPositive x y = PT.map2 λ (δ , δ≤x) (ε , ε≤y) →
  δ ·₊ ε ,
  subst (λ z → z ≤ℝ x · y)
    (mul-rat (fst δ) (fst ε)
    ∙ sym (addIdL (rat (fst (δ ·₊ ε)))))
    (mulPres≤ (rat (fst δ)) x (rat (fst ε)) y
      (<ℝ-weaken 0ℝ x ∣ δ , δ≤x ∣₁)
      (invEq (rat≤rat≃ 0 (fst ε))
        (ℚOrder.<Weaken≤ 0 (fst ε) (snd ε)))
      (subst (λ z → z ≤ℝ x) (addIdL (rat (fst δ))) δ≤x)
      (subst (λ z → z ≤ℝ y) (addIdL (rat (fst ε))) ε≤y))

mulPres<PosR : ∀ x y z →
  0ℝ <ℝ z → x <ℝ y → x · z <ℝ y · z
mulPres<PosR x y z 0<z x<y =
  positiveSub→< (x · z) (y · z)
    (subst (0ℝ <ℝ_)
      (ℝRing.·DistL- y x z)
      (mulPositive (y - x) z (positiveSub x y x<y) 0<z))

mulPres<PosL : ∀ x y z →
  0ℝ <ℝ z → x <ℝ y → z · x <ℝ z · y
mulPres<PosL x y z 0<z x<y =
  subst2 _<ℝ_ (mulComm x z) (mulComm y z)
    (mulPres<PosR x y z 0<z x<y)

mulPres< : ∀ x y z w →
  0ℝ <ℝ y → 0ℝ <ℝ z →
  x <ℝ y → z <ℝ w → x · z <ℝ y · w
mulPres< x y z w 0<y 0<z x<y z<w =
  <ℝ-trans (x · z) (y · z) (y · w)
    (mulPres<PosR x y z 0<z x<y)
    (mulPres<PosL z w y 0<y z<w)
