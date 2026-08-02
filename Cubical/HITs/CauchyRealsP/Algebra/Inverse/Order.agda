module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Archimedean
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Positive

open import Cubical.Relation.Premetric.Mappings

private
  boundedReciprocalMax : ℚ₊ → ℝ → ℝ → ℝ
  boundedReciprocalMax η x y =
    boundedReciprocalℝ η (maxℝ x y)

  boundedReciprocalMin : ℚ₊ → ℝ → ℝ → ℝ
  boundedReciprocalMin η x y =
    minℝ
      (boundedReciprocalℝ η x)
      (boundedReciprocalℝ η y)

  boundedReciprocalMaxLip₁ : ∀ η y →
    isLipschitz
      (snd ℝPremetricSpace)
      (λ x → boundedReciprocalMax η x y)
      (snd ℝPremetricSpace)
  boundedReciprocalMaxLip₁ η y =
    ∣ reciprocalLipschitzBound η ·₊ 1
    , composeRealLipschitzWith
        (boundedReciprocalℝ η)
        (λ x → maxℝ x y)
        (reciprocalLipschitzBound η) 1
        (boundedReciprocalIsLipschitz η)
        (isNonExpanding→isLipschitzWith1
          (snd ℝPremetricSpace)
          (λ x → maxℝ x y)
          (snd ℝPremetricSpace)
          (maxIsNonExpanding₁ y))
    ∣₁

  boundedReciprocalMaxLip₂ : ∀ η x →
    isLipschitz
      (snd ℝPremetricSpace)
      (boundedReciprocalMax η x)
      (snd ℝPremetricSpace)
  boundedReciprocalMaxLip₂ η x =
    ∣ reciprocalLipschitzBound η ·₊ 1
    , composeRealLipschitzWith
        (boundedReciprocalℝ η)
        (maxℝ x)
        (reciprocalLipschitzBound η) 1
        (boundedReciprocalIsLipschitz η)
        (isNonExpanding→isLipschitzWith1
          (snd ℝPremetricSpace)
          (maxℝ x)
          (snd ℝPremetricSpace)
          (maxIsNonExpanding₂ x))
    ∣₁

  boundedReciprocalMinLip₁ : ∀ η y →
    isLipschitz
      (snd ℝPremetricSpace)
      (λ x → boundedReciprocalMin η x y)
      (snd ℝPremetricSpace)
  boundedReciprocalMinLip₁ η y =
    ∣ 1 ·₊ reciprocalLipschitzBound η
    , composeRealLipschitzWith
        (λ u → minℝ u (boundedReciprocalℝ η y))
        (boundedReciprocalℝ η)
        1 (reciprocalLipschitzBound η)
        (isNonExpanding→isLipschitzWith1
          (snd ℝPremetricSpace)
          (λ u → minℝ u (boundedReciprocalℝ η y))
          (snd ℝPremetricSpace)
          (minIsNonExpanding₁
            (boundedReciprocalℝ η y)))
        (boundedReciprocalIsLipschitz η)
    ∣₁

  boundedReciprocalMinLip₂ : ∀ η x →
    isLipschitz
      (snd ℝPremetricSpace)
      (boundedReciprocalMin η x)
      (snd ℝPremetricSpace)
  boundedReciprocalMinLip₂ η x =
    ∣ 1 ·₊ reciprocalLipschitzBound η
    , composeRealLipschitzWith
        (minℝ (boundedReciprocalℝ η x))
        (boundedReciprocalℝ η)
        1 (reciprocalLipschitzBound η)
        (isNonExpanding→isLipschitzWith1
          (snd ℝPremetricSpace)
          (minℝ (boundedReciprocalℝ η x))
          (snd ℝPremetricSpace)
          (minIsNonExpanding₂
            (boundedReciprocalℝ η x)))
        (boundedReciprocalIsLipschitz η)
    ∣₁

  boundedReciprocalMaxℚ : ∀ η p q →
    boundedReciprocalℚ η (ℚ.max p q) ≡
    ℚ.min
      (boundedReciprocalℚ η p)
      (boundedReciprocalℚ η q)
  boundedReciprocalMaxℚ η p q with ℚ.≤Dec p q
  ... | yes p≤q =
    cong (boundedReciprocalℚ η)
      (ℚ.≤→max p q p≤q)
    ∙ sym
        (ℚ.minComm
          (boundedReciprocalℚ η p)
          (boundedReciprocalℚ η q)
        ∙ ℚ.≤→min
            (boundedReciprocalℚ η q)
            (boundedReciprocalℚ η p)
            (ℚInv.invℚ₊≤invℚ₊
              (clampedPositive η q)
              (clampedPositive η p)
              (ℚ.≤MonotoneMax
                (fst η) (fst η) p q
                (ℚ.isRefl≤ (fst η)) p≤q)))
  ... | no ¬p≤q =
    cong (boundedReciprocalℚ η)
      (ℚ.maxComm p q
      ∙ ℚ.≤→max q p q≤p)
    ∙ sym
        (ℚ.≤→min
          (boundedReciprocalℚ η p)
          (boundedReciprocalℚ η q)
          (ℚInv.invℚ₊≤invℚ₊
            (clampedPositive η p)
            (clampedPositive η q)
            (ℚ.≤MonotoneMax
              (fst η) (fst η) q p
              (ℚ.isRefl≤ (fst η)) q≤p)))
    where
    q≤p : q ℚ.≤ p
    q≤p =
      PT.rec
        (ℚ.isProp≤ q p)
        (⊎.rec
          (λ p≤q → ⊥.rec (¬p≤q p≤q))
          (idfun (q ℚ.≤ p)))
        (ℚ.isTotal≤ p q)

  boundedReciprocalMax-rat : ∀ η p q →
    boundedReciprocalMax η (rat p) (rat q) ≡
    boundedReciprocalMin η (rat p) (rat q)
  boundedReciprocalMax-rat η p q =
    cong (boundedReciprocalℝ η)
      (max-rat p q)
    ∙ boundedReciprocal-rat η (ℚ.max p q)
    ∙ cong rat (boundedReciprocalMaxℚ η p q)
    ∙ sym
        (min-rat
          (boundedReciprocalℚ η p)
          (boundedReciprocalℚ η q))
    ∙ cong₂ minℝ
        (sym (boundedReciprocal-rat η p))
        (sym (boundedReciprocal-rat η q))

boundedReciprocalMaxMin : ∀ η x y →
  boundedReciprocalℝ η (maxℝ x y) ≡
  minℝ
    (boundedReciprocalℝ η x)
    (boundedReciprocalℝ η y)
boundedReciprocalMaxMin η =
  lipschitzExtensionality₂
    (boundedReciprocalMax η)
    (boundedReciprocalMin η)
    (boundedReciprocalMaxLip₁ η)
    (boundedReciprocalMaxLip₂ η)
    (boundedReciprocalMinLip₁ η)
    (boundedReciprocalMinLip₂ η)
    (boundedReciprocalMax-rat η)

boundedReciprocalAntitone : ∀ η x y →
  x ≤ℝ y →
  boundedReciprocalℝ η y ≤ℝ
  boundedReciprocalℝ η x
boundedReciprocalAntitone η x y x≤y =
  subst
    (_≤ℝ boundedReciprocalℝ η x)
    minPath
    (min≤left
      (boundedReciprocalℝ η x)
      (boundedReciprocalℝ η y))
  where
  minPath :
    minℝ
      (boundedReciprocalℝ η x)
      (boundedReciprocalℝ η y)
    ≡
    boundedReciprocalℝ η y
  minPath =
    sym (boundedReciprocalMaxMin η x y)
    ∙ cong (boundedReciprocalℝ η)
        (maxOf≤ x y x≤y)

private
  positiveReciprocalPositiveAtUpper :
    ∀ x (p : 0 <ℝ x)
    (w : PositiveGap 0 x)
    (n : ℕ₊₁) →
    x <ℝ rat (naturalRational n) →
    0 <ℝ positiveReciprocal x p
  positiveReciprocalPositiveAtUpper x p w n x<n =
    subst
      (0 <ℝ_)
      (sym positiveReciprocalPath)
      boundedReciprocalPositive
    where
    η : ℚ₊
    η =
      width w

    N : ℚ₊
    N =
      naturalBound n

    x≤N : x ≤ℝ rat (fst N)
    x≤N =
      <ℝ-weaken x (rat (fst N)) x<n

    η≤N-real :
      rat (fst η) ≤ℝ rat (fst N)
    η≤N-real =
      ≤ℝ-trans
        (rat (fst η)) x (rat (fst N))
        (gapLowerBound w) x≤N

    η≤N : fst η ℚ.≤ fst N
    η≤N =
      ≤ℝ→≤ℚ (fst η) (fst N) η≤N-real

    reciprocalAtNaturalPath :
      boundedReciprocalℝ η (rat (fst N)) ≡
      rat (fst (N ⁻¹₊))
    reciprocalAtNaturalPath =
      boundedReciprocal-rat η (fst N)
      ∙ cong rat
          (boundedReciprocalℚAbove
            η (fst N) (snd N) η≤N)

    reciprocalAtNaturalPositive :
      0 <ℝ boundedReciprocalℝ η (rat (fst N))
    reciprocalAtNaturalPositive =
      subst
        (0 <ℝ_)
        (sym reciprocalAtNaturalPath)
        (<ℚ→<ℝ
          0 (fst (N ⁻¹₊)) (snd (N ⁻¹₊)))

    boundedReciprocalPositive :
      0 <ℝ boundedReciprocalℝ η x
    boundedReciprocalPositive =
      <≤ℝ-trans
        0
        (boundedReciprocalℝ η (rat (fst N)))
        (boundedReciprocalℝ η x)
        reciprocalAtNaturalPositive
        (boundedReciprocalAntitone
          η x (rat (fst N)) x≤N)

    positiveReciprocalPath :
      positiveReciprocal x p ≡
      boundedReciprocalℝ η x
    positiveReciprocalPath =
      cong (positiveReciprocal x)
        (isProp<ℝ 0 x p ∣ w ∣₁)
      ∙ positiveReciprocalAtGap x w

positiveReciprocalPositive : ∀ x (p : 0 <ℝ x) →
  0 <ℝ positiveReciprocal x p
positiveReciprocalPositive x p =
  PT.rec
    (isProp<ℝ 0 (positiveReciprocal x p))
    (λ w →
      PT.rec
        (isProp<ℝ 0 (positiveReciprocal x p))
        (λ { (n , x<n) →
          positiveReciprocalPositiveAtUpper
            x p w n x<n })
        (∃naturalUpperBound x))
    p

private
  positiveReciprocalComparisonPaths :
    ∀ x y (px : 0 <ℝ x) (py : 0 <ℝ y) →
    let
      x⁻¹ = positiveReciprocal x px
      y⁻¹ = positiveReciprocal y py
      z = x⁻¹ · y⁻¹
    in
      (x · z ≡ y⁻¹) ×
      (y · z ≡ x⁻¹)
  positiveReciprocalComparisonPaths x y px py =
    (sym
      (mulAssoc x x⁻¹ y⁻¹)
    ∙ cong (_· y⁻¹)
        (positiveReciprocalLaw x px)
    ∙ mulIdL y⁻¹)
    ,
    (cong (y ·_)
      (mulComm x⁻¹ y⁻¹)
    ∙ sym
        (mulAssoc y y⁻¹ x⁻¹)
    ∙ cong (_· x⁻¹)
        (positiveReciprocalLaw y py)
    ∙ mulIdL x⁻¹)
    where
    x⁻¹ : ℝ
    x⁻¹ =
      positiveReciprocal x px

    y⁻¹ : ℝ
    y⁻¹ =
      positiveReciprocal y py

positiveReciprocalAntitone : ∀ x y
  (px : 0 <ℝ x) (py : 0 <ℝ y) →
  x ≤ℝ y →
  positiveReciprocal y py ≤ℝ
  positiveReciprocal x px
positiveReciprocalAntitone x y px py x≤y =
  subst2 _≤ℝ_ leftPath rightPath
    (mulMonoR≤ x y z 0≤z x≤y)
  where
  x⁻¹ y⁻¹ z : ℝ
  x⁻¹ =
    positiveReciprocal x px
  y⁻¹ =
    positiveReciprocal y py
  z =
    x⁻¹ · y⁻¹

  0≤z : 0 ≤ℝ z
  0≤z =
    <ℝ-weaken 0 z
      (mulPositive x⁻¹ y⁻¹
        (positiveReciprocalPositive x px)
        (positiveReciprocalPositive y py))

  leftPath : x · z ≡ y⁻¹
  leftPath =
    fst (positiveReciprocalComparisonPaths x y px py)

  rightPath : y · z ≡ x⁻¹
  rightPath =
    snd (positiveReciprocalComparisonPaths x y px py)

positiveReciprocalStrictAntitone : ∀ x y
  (px : 0 <ℝ x) (py : 0 <ℝ y) →
  x <ℝ y →
  positiveReciprocal y py <ℝ
  positiveReciprocal x px
positiveReciprocalStrictAntitone x y px py x<y =
  subst2 _<ℝ_ leftPath rightPath
    (mulMonoR< x y z 0<z x<y)
  where
  x⁻¹ y⁻¹ z : ℝ
  x⁻¹ =
    positiveReciprocal x px
  y⁻¹ =
    positiveReciprocal y py
  z =
    x⁻¹ · y⁻¹

  0<z : 0 <ℝ z
  0<z =
    mulPositive x⁻¹ y⁻¹
      (positiveReciprocalPositive x px)
      (positiveReciprocalPositive y py)

  leftPath : x · z ≡ y⁻¹
  leftPath =
    fst (positiveReciprocalComparisonPaths x y px py)

  rightPath : y · z ≡ x⁻¹
  rightPath =
    snd (positiveReciprocalComparisonPaths x y px py)
