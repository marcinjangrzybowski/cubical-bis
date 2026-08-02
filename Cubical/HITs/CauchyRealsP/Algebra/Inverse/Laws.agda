module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Bounded

open import Cubical.Relation.Premetric.Mappings

positiveClamp : ℚ₊ → ℝ → ℝ
positiveClamp η x =
  maxℝ (rat (fst η)) x

positiveClamp-rat : ∀ η q →
  positiveClamp η (rat q) ≡
  rat (fst (clampedPositive η q))
positiveClamp-rat η q =
  max-rat (fst η) q

positiveClampIsNonExpanding : ∀ η →
  IsNonExpanding
    (snd ℝPremetricSpace)
    (positiveClamp η)
    (snd ℝPremetricSpace)
positiveClampIsNonExpanding η =
  maxIsNonExpanding₂ (rat (fst η))

positiveClampIsContinuous : ∀ η →
  isContinuous
    (snd ℝPremetricSpace)
    (positiveClamp η)
    (snd ℝPremetricSpace)
positiveClampIsContinuous η =
  isNonExpanding→isContinuous
    (snd ℝPremetricSpace)
    (positiveClamp η)
    (snd ℝPremetricSpace)
    (positiveClampIsNonExpanding η)

boundedReciprocalAfterClamp : ℚ₊ → ℝ → ℝ
boundedReciprocalAfterClamp η x =
  boundedReciprocalℝ η (positiveClamp η x)

boundedReciprocalAfterClampIsLipschitz : ∀ η →
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (boundedReciprocalAfterClamp η)
    (snd ℝPremetricSpace)
    (reciprocalLipschitzBound η)
boundedReciprocalAfterClampIsLipschitz η
  .IsLipschitzWith.pres≈ x y ε x∼y =
    IsLipschitzWith.pres≈
      (boundedReciprocalIsLipschitz η)
      (positiveClamp η x)
      (positiveClamp η y)
      ε
      (IsNonExpanding.pres≈
        (positiveClampIsNonExpanding η)
        x y ε x∼y)

boundedReciprocalAfterClampIsContinuous : ∀ η →
  isContinuous
    (snd ℝPremetricSpace)
    (boundedReciprocalAfterClamp η)
    (snd ℝPremetricSpace)
boundedReciprocalAfterClampIsContinuous η =
  isLipschitz→isContinuous
    (snd ℝPremetricSpace)
    (boundedReciprocalAfterClamp η)
    (snd ℝPremetricSpace)
    ∣ reciprocalLipschitzBound η ,
      boundedReciprocalAfterClampIsLipschitz η ∣₁

private
  constantOneIsNonExpanding :
    IsNonExpanding
      (snd ℝPremetricSpace)
      (λ _ → 1)
      (snd ℝPremetricSpace)
  constantOneIsNonExpanding
    .IsNonExpanding.pres≈ _ _ ε _ =
      refl∼ 1 ε

  constantOneIsContinuous :
    isContinuous
      (snd ℝPremetricSpace)
      (λ _ → 1)
      (snd ℝPremetricSpace)
  constantOneIsContinuous =
    isNonExpanding→isContinuous
      (snd ℝPremetricSpace)
      (λ _ → 1)
      (snd ℝPremetricSpace)
      constantOneIsNonExpanding

  clampedReciprocalProduct : ℚ₊ → ℝ → ℝ
  clampedReciprocalProduct η x =
    positiveClamp η x · boundedReciprocalAfterClamp η x

  clampedReciprocalProductIsContinuous : ∀ η →
    isContinuous
      (snd ℝPremetricSpace)
      (clampedReciprocalProduct η)
      (snd ℝPremetricSpace)
  clampedReciprocalProductIsContinuous η =
    mulOfContinuousIsContinuous
      (snd ℝPremetricSpace)
      (positiveClamp η)
      (boundedReciprocalAfterClamp η)
      (positiveClampIsContinuous η)
      (boundedReciprocalAfterClampIsContinuous η)

  clampedReciprocalProduct-rat : ∀ η q →
    clampedReciprocalProduct η (rat q) ≡ 1
  clampedReciprocalProduct-rat η q =
    cong₂ _·_
      (positiveClamp-rat η q)
      (cong (boundedReciprocalℝ η)
        (positiveClamp-rat η q)
      ∙ boundedReciprocal-rat η (fst r))
    ∙ mul-rat (fst r) (boundedReciprocalℚ η (fst r))
    ∙ cong rat
        (cong (fst r ℚ.·_)
          (boundedReciprocalℚAbove
            η (fst r) (snd r)
            (ℚ.≤max (fst η) q))
        ∙ ℚInv.x·invℚ₊[x] r)
    where
    r : ℚ₊
    r =
      clampedPositive η q

clampedReciprocalLaw : ∀ η x →
  positiveClamp η x · boundedReciprocalAfterClamp η x ≡ 1
clampedReciprocalLaw η =
  funExt⁻
    (continuousExtensionality
      ℝPremetricSpace
      (clampedReciprocalProduct η)
      (λ _ → 1)
      (clampedReciprocalProductIsContinuous η)
      constantOneIsContinuous
      (clampedReciprocalProduct-rat η))

boundedReciprocalLaw : ∀ η x →
  rat (fst η) ≤ℝ x →
  x · boundedReciprocalℝ η x ≡ 1
boundedReciprocalLaw η x η≤x =
  sym
    (cong₂ _·_
      clampFix
      (cong (boundedReciprocalℝ η) clampFix))
  ∙ clampedReciprocalLaw η x
  where
  clampFix :
    positiveClamp η x ≡ x
  clampFix =
    maxOf≤ (rat (fst η)) x η≤x
