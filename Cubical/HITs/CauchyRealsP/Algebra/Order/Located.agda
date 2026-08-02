module Cubical.HITs.CauchyRealsP.Algebra.Order.Located where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

import Cubical.Functions.Logic as L

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Density

maxStrictUpper : ∀ x y z →
  x <ℝ z → y <ℝ z → maxℝ x y <ℝ z
maxStrictUpper x y z =
  PT.map2 combine
  where
  combine :
    PositiveGap x z → PositiveGap y z →
    PositiveGap (maxℝ x y) z
  combine u v =
    positiveGap κ
      (gapBoundIntro (maxℝ x y) z κ
        (subst
          (_≤ℝ z)
          (sym
            (maxAddDistribR x y (rat (fst κ))))
          (max≤
            (x + rat (fst κ))
            (y + rat (fst κ))
            z
            x+κ≤z y+κ≤z)))
    where
    κ : ℚ₊
    κ = min₊ (width u) (width v)

    κ≤u : fst κ ℚ.≤ fst (width u)
    κ≤u = ℚ.min≤ (fst (width u)) (fst (width v))

    κ≤v : fst κ ℚ.≤ fst (width v)
    κ≤v = ℚ.min≤' (fst (width u)) (fst (width v))

    x+κ≤z : x + rat (fst κ) ≤ℝ z
    x+κ≤z =
      ≤ℝ-trans
        (x + rat (fst κ))
        (x + rat (fst (width u)))
        z
        (≤ℝ-addL
          (rat (fst κ)) (rat (fst (width u))) x
          (≤ℚ→≤ℝ (fst κ) (fst (width u)) κ≤u))
        (gapBoundElim x z (width u) (bound u))

    y+κ≤z : y + rat (fst κ) ≤ℝ z
    y+κ≤z =
      ≤ℝ-trans
        (y + rat (fst κ))
        (y + rat (fst (width v)))
        z
        (≤ℝ-addL
          (rat (fst κ)) (rat (fst (width v))) y
          (≤ℚ→≤ℝ (fst κ) (fst (width v)) κ≤v))
          (gapBoundElim y z (width v) (bound v))

minStrictLower : ∀ x y z →
  z <ℝ x → z <ℝ y → z <ℝ minℝ x y
minStrictLower x y z z<x z<y =
  subst
    (_<ℝ minℝ x y)
    (negInvol z)
    (<ℝ-neg
      (maxℝ (- x) (- y)) (- z)
      (maxStrictUpper
        (- x) (- y) (- z)
        (<ℝ-neg z x z<x)
        (<ℝ-neg z y z<y)))

dichotomyℝ : ∀ x y z →
  x <ℝ z → ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
dichotomyℝ x y z =
  PT.rec squash₁ dichotomyFromGap
  where
  dichotomyFromGap :
    PositiveGap x z →
    ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
  dichotomyFromGap w =
    PT.map2 compare
      (denseℚinℝ x (x + rat (fst half)) x<x+half)
      (denseℚinℝ (y - rat (fst half)) y y-half<y)
    where
    δ : ℚ₊
    δ = width w

    half : ℚ₊
    half = δ /2₊

    x<x+half : x <ℝ x + rat (fst half)
    x<x+half =
      subst
        (_<ℝ x + rat (fst half))
        (addIdR x)
        (<ℝ-addL
          0 (rat (fst half)) x
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    y-half<y : y - rat (fst half) <ℝ y
    y-half<y =
      subst2 _<ℝ_
        (addIdR (y - rat (fst half)))
        (subAddCancel y (rat (fst half)))
        (<ℝ-addL
          0 (rat (fst half))
          (y - rat (fst half))
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    x+halvesPath :
      (x + rat (fst half)) + rat (fst half) ≡
      x + rat (fst δ)
    x+halvesPath =
      sym (addAssoc x (rat (fst half)) (rat (fst half)))
      ∙ cong (x +_)
          (rat+rat (fst half) (fst half)
          ∙ cong rat (1/2∈ℚ./2+/2≡id (fst δ)))

    compare :
      (Σ[ a ∈ ℚ ]
        (x <ℝ rat a) ×
        (rat a <ℝ x + rat (fst half))) →
      (Σ[ b ∈ ℚ ]
        (y - rat (fst half) <ℝ rat b) ×
        (rat b <ℝ y)) →
      (y <ℝ z) ⊎ (x <ℝ y)
    compare (a , x<a , a<x+half)
            (b , y-half<b , b<y) =
      ⊎.rec b≤aCase a<bCase (ℚ.Dichotomyℚ b a)
      where
      b≤aCase : b ℚ.≤ a → (y <ℝ z) ⊎ (x <ℝ y)
      b≤aCase b≤a =
        inl
          (<≤ℝ-trans
            y (x + rat (fst δ)) z
            y<x+δ
            (gapBoundElim x z δ (bound w)))
        where
        y-half<x+half :
          y - rat (fst half) <ℝ x + rat (fst half)
        y-half<x+half =
          <ℝ-trans
            (y - rat (fst half))
            (rat a)
            (x + rat (fst half))
            (<≤ℝ-trans
              (y - rat (fst half))
              (rat b) (rat a)
              y-half<b
              (≤ℚ→≤ℝ b a b≤a))
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

      a<bCase : a ℚ.< b → (y <ℝ z) ⊎ (x <ℝ y)
      a<bCase a<b =
        inr
          (<ℝ-trans
            x (rat b) y
            (<ℝ-trans
              x (rat a) (rat b)
              x<a (<ℚ→<ℝ a b a<b))
            b<y)

arbitrarilySmallSlack→≤ : ∀ x y →
  (∀ ε → x <ℝ y + rat (fst ε)) →
  x ≤ℝ y
arbitrarilySmallSlack→≤ x y x<y+ε =
  maxPath→≤ℝ x y
    (eqℝ (maxℝ x y) y closeAtEveryRadius)
  where
  closeAtEveryRadius : ∀ ε → maxℝ x y ∼[ ε ] y
  closeAtEveryRadius ε =
    absDifference<→closeness
      (maxℝ x y) y ε
      (subst
        (_<ℝ rat (fst ε))
        (sym
          (absOfNonnegative
            (maxℝ x y - y)
            (nonnegativeSub y (maxℝ x y)
              (right≤max x y))))
        difference<ε)
    where
    y<y+ε : y <ℝ y + rat (fst ε)
    y<y+ε =
      subst
        (_<ℝ y + rat (fst ε))
        (addIdR y)
        (<ℝ-addL
          0 (rat (fst ε)) y
          (<ℚ→<ℝ 0 (fst ε) (snd ε)))

    max<y+ε : maxℝ x y <ℝ y + rat (fst ε)
    max<y+ε =
      maxStrictUpper x y (y + rat (fst ε))
        (x<y+ε ε) y<y+ε

    cancelYPath :
      (y + rat (fst ε)) + (- y) ≡ rat (fst ε)
    cancelYPath =
      sym (addAssoc y (rat (fst ε)) (- y))
      ∙ cong (y +_) (addComm (rat (fst ε)) (- y))
      ∙ addAssoc y (- y) (rat (fst ε))
      ∙ cong (_+ rat (fst ε)) (addInvR y)
      ∙ addIdL (rat (fst ε))

    difference<ε :
      maxℝ x y - y <ℝ rat (fst ε)
    difference<ε =
      subst2 _<ℝ_ refl cancelYPath
        (<ℝ-addR
          (maxℝ x y)
          (y + rat (fst ε))
          (- y)
          max<y+ε)

≤ℝ→notGreater : ∀ x y →
  x ≤ℝ y → ¬ (y <ℝ x)
≤ℝ→notGreater x y x≤y y<x =
  <ℝ-asym y x y<x
    (subst2 _<ℝ_
      (sym x≡y) x≡y y<x)
  where
  x≡y : x ≡ y
  x≡y =
    ≤ℝ-antisym x y x≤y (<ℝ-weaken y x y<x)

notGreater→≤ℝ : ∀ x y →
  ¬ (y <ℝ x) → x ≤ℝ y
notGreater→≤ℝ x y not-y<x =
  arbitrarilySmallSlack→≤ x y λ ε →
    PT.rec
      (isProp<ℝ x (y + rat (fst ε)))
      (⊎.rec (idfun _) (⊥.rec ∘ not-y<x))
      (dichotomyℝ
        y x (y + rat (fst ε))
        (subst
          (_<ℝ y + rat (fst ε))
          (addIdR y)
          (<ℝ-addL
            0 (rat (fst ε)) y
            (<ℚ→<ℝ 0 (fst ε) (snd ε)))))

≤notGreaterEquiv : ∀ x y →
  (x ≤ℝ y) ≃ (¬ (y <ℝ x))
≤notGreaterEquiv x y =
  propBiimpl→Equiv
    {A = x ≤ℝ y} {B = ¬ (y <ℝ x)}
    (isProp≤ℝ x y)
    (isPropΠ λ _ → isProp⊥)
    (≤ℝ→notGreater x y)
    (notGreater→≤ℝ x y)

isWeaklyLinear<ℝ : BinaryRelation.isWeaklyLinear _<ℝ_
isWeaklyLinear<ℝ x y z x<y =
  PT.map
    (⊎.rec inr inl)
    (dichotomyℝ x z y x<y)

positiveSum→positiveSummand : ∀ x y →
  0 <ℝ x + y → (0 <ℝ x) L.⊔′ (0 <ℝ y)
positiveSum→positiveSummand x y 0<x+y =
  PT.map
    (⊎.rec (inr ∘ x<x+y→0<y) inl)
    (dichotomyℝ 0 x (x + y) 0<x+y)
  where
  x<x+y→0<y : x <ℝ x + y → 0 <ℝ y
  x<x+y→0<y x<x+y =
    <ℝ-addR-cancel 0 y x
      (subst2 _<ℝ_
        (sym (addIdL x))
        (addComm x y)
        x<x+y)
