module Cubical.Analysis.Real.Algebra.Inverse.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded
open import Cubical.Analysis.Real.Algebra.Inverse.Compatibility

open PositiveRationals


positiveClampIsContinuous : ∀ η →
  isContinuous
    (ℝPremetricSpace .snd) (positiveClamp η)
    (ℝPremetricSpace .snd)
positiveClampIsContinuous η =
  isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (positiveClamp η)
    (ℝPremetricSpace .snd)
    (positiveClampIsNonExpanding η)


boundedReciprocalAfterClamp : ℚ₊ → ℝ → ℝ
boundedReciprocalAfterClamp η x =
  boundedReciprocalℝ η (positiveClamp η x)


boundedReciprocalAfterClampIsLipschitz : ∀ η →
  IsLipschitzWith
    (ℝPremetricSpace .snd)
    (boundedReciprocalAfterClamp η)
    (ℝPremetricSpace .snd)
    (reciprocalLipschitzBound η)
boundedReciprocalAfterClampIsLipschitz η
  .IsLipschitzWith.pres≈ x y ε x∼y =
    boundedReciprocalIsLipschitz η .IsLipschitzWith.pres≈
      (positiveClamp η x) (positiveClamp η y) ε
      (positiveClampIsNonExpanding η
        .IsNonExpanding.pres≈ x y ε x∼y)


boundedReciprocalAfterClampIsContinuous : ∀ η →
  isContinuous
    (ℝPremetricSpace .snd)
    (boundedReciprocalAfterClamp η)
    (ℝPremetricSpace .snd)
boundedReciprocalAfterClampIsContinuous η =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd)
    (boundedReciprocalAfterClamp η)
    (ℝPremetricSpace .snd)
    ∣ reciprocalLipschitzBound η ,
      boundedReciprocalAfterClampIsLipschitz η ∣₁


private
  constantOneIsNonExpanding :
    IsNonExpanding
      (ℝPremetricSpace .snd)
      (λ _ → 1ℝ)
      (ℝPremetricSpace .snd)
  constantOneIsNonExpanding
    .IsNonExpanding.pres≈ _ _ ε _ = refl∼ 1ℝ ε

  constantOneIsContinuous :
    isContinuous
      (ℝPremetricSpace .snd)
      (λ _ → 1ℝ)
      (ℝPremetricSpace .snd)
  constantOneIsContinuous =
    isNonExpanding→isContinuous
      (ℝPremetricSpace .snd)
      (λ _ → 1ℝ)
      (ℝPremetricSpace .snd)
      constantOneIsNonExpanding

  clampedReciprocalProduct : ℚ₊ → ℝ → ℝ
  clampedReciprocalProduct η x =
    positiveClamp η x · boundedReciprocalAfterClamp η x

  clampedReciprocalProductIsContinuous : ∀ η →
    isContinuous
      (ℝPremetricSpace .snd)
      (clampedReciprocalProduct η)
      (ℝPremetricSpace .snd)
  clampedReciprocalProductIsContinuous η =
    mulOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (positiveClamp η)
      (boundedReciprocalAfterClamp η)
      (positiveClampIsContinuous η)
      (boundedReciprocalAfterClampIsContinuous η)

  clampedReciprocalProduct-rat : ∀ η q →
    clampedReciprocalProduct η (rat q) ≡ 1ℝ
  clampedReciprocalProduct-rat η q =
      cong₂ _·_
        (positiveClamp-rat η q)
        (cong (boundedReciprocalℝ η) (positiveClamp-rat η q)
        ∙ boundedReciprocal-rat η (fst r))
    ∙ mul-rat (fst r) (boundedReciprocalℚ η (fst r))
    ∙ cong rat
        (cong (fst r ℚ.·_)
          (boundedReciprocalℚAbove
            η (fst r) (snd r) (ℚ.≤max (fst η) q))
        ∙ ℚInv.x·invℚ₊[x] r)
    where
    r : ℚ₊
    r = clampedPositive η q


clampedReciprocalLaw : ∀ η x →
  positiveClamp η x · boundedReciprocalℝ η (positiveClamp η x)
    ≡ 1ℝ
clampedReciprocalLaw η =
  funExt⁻
    (continuousExtensionality
      (λ x → positiveClamp η x ·
        boundedReciprocalℝ η (positiveClamp η x))
      (λ _ → 1ℝ)
      (clampedReciprocalProductIsContinuous η)
      constantOneIsContinuous
      (clampedReciprocalProduct-rat η))


boundedReciprocalLaw : ∀ η x →
  rat (fst η) ≤ℝ x →
  x · boundedReciprocalℝ η x ≡ 1ℝ
boundedReciprocalLaw η x η≤x =
    sym
      (cong₂ _·_
        clampFix (cong (boundedReciprocalℝ η) clampFix))
  ∙ clampedReciprocalLaw η x
  where
  clampFix : positiveClamp η x ≡ x
  clampFix = η≤x
