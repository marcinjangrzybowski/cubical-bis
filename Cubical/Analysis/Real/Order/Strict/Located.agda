module Cubical.Analysis.Real.Order.Strict.Located where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_; invEq; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels using (isPropΠ)

import Cubical.Functions.Logic as L

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary using (¬_)

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base
  using (ℝ; rat; _∼[_]_; eqℝ)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addComm; addIdR; addIdL; addAssoc)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
  using (_-_; addInvR; addInvL)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Algebra.Lattice using (maxℝ)
open import Cubical.Analysis.Real.Order.Base
  using
    ( _≤ℝ_; isProp≤ℝ; ≤ℝ-trans; rat≤rat≃
    ; right≤max; maxLeastUpperBound
    )
open import Cubical.Analysis.Real.Order.Addition
  using (addMax; addPres≤L)
open import Cubical.Analysis.Real.Order.AbsoluteValue
  using (absOfNonnegative; nonnegativeSub)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
  using (absDifference<→closeness)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-trans; <≤ℝ-trans; ≤ℝ→≯)
open import Cubical.Analysis.Real.Order.Strict.Addition
  using (<ℝ-addR; <ℝ-addL; <ℝ-addR-cancel)
open import Cubical.Analysis.Real.Order.Strict.Density using (denseℚinℝ)

open ℚInstance.PositiveRationals
  using (ℚ₊; min₊; min₊≤L; min₊≤R)
open ℚInstance.PositiveRationals.PositiveHalvesℚ using (_/2₊)


private
  rationalDichotomy : ∀ a b →
    (a ℚOrder.≤ b) ⊎ (b ℚOrder.< a)
  rationalDichotomy a b with a ℚOrder.≟ b
  ... | ℚOrder.lt a<b = inl (ℚOrder.<Weaken≤ a b a<b)
  ... | ℚOrder.eq a≡b = inl (ℚOrder.≡Weaken≤ a b a≡b)
  ... | ℚOrder.gt b<a = inr b<a

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


maxStrictUpper : ∀ x y z →
  x <ℝ z → y <ℝ z → maxℝ x y <ℝ z
maxStrictUpper x y z = PT.map2 combine
  where
  combine :
    PositiveGap x z → PositiveGap y z →
    PositiveGap (maxℝ x y) z
  combine (δ , x+δ≤z) (ε , y+ε≤z) =
    κ ,
      subst (_≤ℝ z) (sym (addMax x y (rat (fst κ))))
        (maxLeastUpperBound
          (x + rat (fst κ)) (y + rat (fst κ)) z
          x+κ≤z y+κ≤z)
    where
    κ : ℚ₊
    κ = min₊ δ ε

    x+κ≤z : x + rat (fst κ) ≤ℝ z
    x+κ≤z = ≤ℝ-trans
      (x + rat (fst κ)) (x + rat (fst δ)) z
      (addPres≤L (rat (fst κ)) (rat (fst δ)) x
        (invEq (rat≤rat≃ (fst κ) (fst δ)) (min₊≤L δ ε)))
      x+δ≤z

    y+κ≤z : y + rat (fst κ) ≤ℝ z
    y+κ≤z = ≤ℝ-trans
      (y + rat (fst κ)) (y + rat (fst ε)) z
      (addPres≤L (rat (fst κ)) (rat (fst ε)) y
        (invEq (rat≤rat≃ (fst κ) (fst ε)) (min₊≤R δ ε)))
      y+ε≤z


dichotomyℝ : ∀ x y z →
  x <ℝ z → ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
dichotomyℝ x y z = PT.rec squash₁ dichotomyFromGap
  where
  dichotomyFromGap :
    PositiveGap x z → ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
  dichotomyFromGap (δ , x+δ≤z) =
    PT.map2 compare
      (denseℚinℝ x (x + rat (fst half)) x<x+half)
      (denseℚinℝ (y - rat (fst half)) y y-half<y)
    where
    half : ℚ₊
    half = δ /2₊

    x<x+half : x <ℝ x + rat (fst half)
    x<x+half =
      subst (_<ℝ x + rat (fst half)) (addIdR x)
        (<ℝ-addL 0ℝ (rat (fst half)) x
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    y-half<y : y - rat (fst half) <ℝ y
    y-half<y =
      subst2 _<ℝ_
        (addIdR (y - rat (fst half)))
        (subAddCancel y (rat (fst half)))
        (<ℝ-addL 0ℝ (rat (fst half))
          (y - rat (fst half))
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    x+halvesPath :
      (x + rat (fst half)) + rat (fst half) ≡
      x + rat (fst δ)
    x+halvesPath =
      sym (addAssoc x (rat (fst half)) (rat (fst half)))
      ∙ cong (x +_)
          (rat+rat (fst half) (fst half)
          ∙ cong rat
              (ℚInstance.1/2∈ℚ./2+/2≡id (fst δ)))

    compare :
      (Σ[ a ∈ ℚ ]
        (x <ℝ rat a) × (rat a <ℝ x + rat (fst half))) →
      (Σ[ b ∈ ℚ ]
        (y - rat (fst half) <ℝ rat b) × (rat b <ℝ y)) →
      (y <ℝ z) ⊎ (x <ℝ y)
    compare (a , x<a , a<x+half)
            (b , y-half<b , b<y) =
      ⊎.rec b≤aCase a<bCase (rationalDichotomy b a)
      where
      b≤aCase : b ℚOrder.≤ a → (y <ℝ z) ⊎ (x <ℝ y)
      b≤aCase b≤a = inl
        (<≤ℝ-trans y (x + rat (fst δ)) z y<x+δ x+δ≤z)
        where
        y-half<x+half :
          y - rat (fst half) <ℝ x + rat (fst half)
        y-half<x+half =
          <ℝ-trans
            (y - rat (fst half)) (rat a)
            (x + rat (fst half))
            (<≤ℝ-trans
              (y - rat (fst half)) (rat b) (rat a)
              y-half<b
              (invEq (rat≤rat≃ b a) b≤a))
            a<x+half

        y<x+δ : y <ℝ x + rat (fst δ)
        y<x+δ =
          subst2 _<ℝ_
            (subAddCancel y (rat (fst half)))
            x+halvesPath
            (<ℝ-addR
              (y - rat (fst half))
              (x + rat (fst half))
              (rat (fst half))
              y-half<x+half)

      a<bCase : a ℚOrder.< b → (y <ℝ z) ⊎ (x <ℝ y)
      a<bCase a<b = inr
        (<ℝ-trans x (rat b) y
          (<ℝ-trans x (rat a) (rat b)
            x<a (<ℚ→<ℝ a b a<b))
          b<y)

isWeaklyLinear<ℝ : ∀ x y z →
  x <ℝ y → ∥ (x <ℝ z) ⊎ (z <ℝ y) ∥₁
isWeaklyLinear<ℝ x y z x<y =
  PT.map (⊎.rec inr inl) (dichotomyℝ x z y x<y)

arbitrarilySmallSlack→≤ : ∀ x y →
  (∀ ε → x <ℝ y + rat (fst ε)) → x ≤ℝ y
arbitrarilySmallSlack→≤ x y x<y+ε =
  eqℝ (maxℝ x y) y closeAtEveryRadius
  where
  closeAtEveryRadius : ∀ ε → maxℝ x y ∼[ ε ] y
  closeAtEveryRadius ε =
    absDifference<→closeness (maxℝ x y) y ε
      (subst
        (_<ℝ rat (fst ε))
        (sym
          (absOfNonnegative
            (maxℝ x y - y)
            (nonnegativeSub y (maxℝ x y) (right≤max x y))))
        difference<ε)
    where
    y<y+ε : y <ℝ y + rat (fst ε)
    y<y+ε =
      subst (_<ℝ y + rat (fst ε)) (addIdR y)
        (<ℝ-addL 0ℝ (rat (fst ε)) y
          (<ℚ→<ℝ 0 (fst ε) (snd ε)))

    max<y+ε : maxℝ x y <ℝ y + rat (fst ε)
    max<y+ε = maxStrictUpper x y (y + rat (fst ε))
      (x<y+ε ε) y<y+ε

    cancelYPath :
      (y + rat (fst ε)) + (- y) ≡ rat (fst ε)
    cancelYPath =
      sym (addAssoc y (rat (fst ε)) (- y))
      ∙ cong (y +_) (addComm (rat (fst ε)) (- y))
      ∙ addAssoc y (- y) (rat (fst ε))
      ∙ cong (_+ rat (fst ε)) (addInvR y)
      ∙ addIdL (rat (fst ε))

    difference<ε : maxℝ x y - y <ℝ rat (fst ε)
    difference<ε = subst ((maxℝ x y - y) <ℝ_) cancelYPath
      (<ℝ-addR
        (maxℝ x y) (y + rat (fst ε)) (- y) max<y+ε)

≤ℝ→notGreater : ∀ x y → x ≤ℝ y → ¬ (y <ℝ x)
≤ℝ→notGreater = ≤ℝ→≯

notGreater→≤ℝ : ∀ x y → ¬ (y <ℝ x) → x ≤ℝ y
notGreater→≤ℝ x y not-y<x =
  arbitrarilySmallSlack→≤ x y λ ε →
    PT.rec
      (isProp<ℝ x (y + rat (fst ε)))
      (⊎.rec (λ x<y+ε → x<y+ε)
        (λ y<x → ⊥.rec (not-y<x y<x)))
      (dichotomyℝ y x (y + rat (fst ε))
        (subst (_<ℝ y + rat (fst ε)) (addIdR y)
          (<ℝ-addL 0ℝ (rat (fst ε)) y
            (<ℚ→<ℝ 0 (fst ε) (snd ε)))))

≤notGreaterEquiv : ∀ x y → (x ≤ℝ y) ≃ (¬ (y <ℝ x))
≤notGreaterEquiv x y = propBiimpl→Equiv
  (isProp≤ℝ x y) (isPropΠ λ _ → isProp⊥)
  (≤ℝ→notGreater x y) (notGreater→≤ℝ x y)

positiveSum→positiveSummand : ∀ x y →
  0ℝ <ℝ x + y → (0ℝ <ℝ x) L.⊔′ (0ℝ <ℝ y)
positiveSum→positiveSummand x y 0<x+y =
  PT.map
    (⊎.rec (λ x<x+y → inr (x<x+y→0<y x<x+y)) inl)
    (dichotomyℝ 0ℝ x (x + y) 0<x+y)
  where
  x<x+y→0<y : x <ℝ x + y → 0ℝ <ℝ y
  x<x+y→0<y x<x+y =
    <ℝ-addR-cancel 0ℝ y x
      (subst2 _<ℝ_
        (sym (addIdL x))
        (addComm x y)
        x<x+y)
