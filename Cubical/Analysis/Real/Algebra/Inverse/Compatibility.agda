module Cubical.Analysis.Real.Algebra.Inverse.Compatibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚData
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded

open PositiveRationals


commonReciprocalLowerBound : ℚ₊ → ℚ₊ → ℚ₊
commonReciprocalLowerBound η θ = clampedPositive η (fst θ)


positiveClamp : ℚ₊ → ℝ → ℝ
positiveClamp η x = maxℝ (rat (fst η)) x


positiveClamp-rat : ∀ η q →
  positiveClamp η (rat q) ≡ rat (ℚ.max (fst η) q)
positiveClamp-rat η q = max-rat (fst η) q


positiveClampIsNonExpanding : ∀ η →
  IsNonExpanding
    (ℝPremetricSpace .snd) (positiveClamp η)
    (ℝPremetricSpace .snd)
positiveClampIsNonExpanding η =
  max-isNonExpanding₂ (rat (fst η))


private
  boundedReciprocalAfterClamp : ℚ₊ → ℚ₊ → ℝ → ℝ
  boundedReciprocalAfterClamp η common x =
    boundedReciprocalℝ η (positiveClamp common x)

  boundedReciprocalAfterClampIsLipschitz : ∀ η common →
    IsLipschitzWith
      (ℝPremetricSpace .snd)
      (boundedReciprocalAfterClamp η common)
      (ℝPremetricSpace .snd)
      (reciprocalLipschitzBound η)
  boundedReciprocalAfterClampIsLipschitz η common
    .IsLipschitzWith.pres≈ x y ε x∼y =
      boundedReciprocalIsLipschitz η .IsLipschitzWith.pres≈
        (positiveClamp common x) (positiveClamp common y) ε
        (positiveClampIsNonExpanding common
          .IsNonExpanding.pres≈ x y ε x∼y)

  boundedReciprocalAfterClampIsContinuous : ∀ η common →
    isContinuous
      (ℝPremetricSpace .snd)
      (boundedReciprocalAfterClamp η common)
      (ℝPremetricSpace .snd)
  boundedReciprocalAfterClampIsContinuous η common =
    isLipschitz→isContinuous
      (ℝPremetricSpace .snd)
      (boundedReciprocalAfterClamp η common)
      (ℝPremetricSpace .snd)
      ∣ reciprocalLipschitzBound η ,
        boundedReciprocalAfterClampIsLipschitz η common ∣₁

  commonContainsLeft : ∀ η θ →
    fst η ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsLeft η θ = ℚ.≤max (fst η) (fst θ)

  commonContainsRight : ∀ η θ →
    fst θ ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsRight η θ = ℚ.≤max' (fst η) (fst θ)

  boundedReciprocalAfterClamp-rat : ∀ η θ q →
    boundedReciprocalAfterClamp
      η (commonReciprocalLowerBound η θ) (rat q)
    ≡
    boundedReciprocalAfterClamp
      θ (commonReciprocalLowerBound η θ) (rat q)
  boundedReciprocalAfterClamp-rat η θ q =
      cong (boundedReciprocalℝ η) (positiveClamp-rat common q)
    ∙ boundedReciprocal-rat η (ℚ.max (fst common) q)
    ∙ cong rat
        (boundedReciprocalℚAbove
          η (ℚ.max (fst common) q)
          (snd commonAtQ)
          (ℚ.isTrans≤
            (fst η) (fst common) (ℚ.max (fst common) q)
            (commonContainsLeft η θ)
            (ℚ.≤max (fst common) q)))
    ∙ sym
        (cong rat
          (boundedReciprocalℚAbove
            θ (ℚ.max (fst common) q)
            (snd commonAtQ)
            (ℚ.isTrans≤
              (fst θ) (fst common) (ℚ.max (fst common) q)
              (commonContainsRight η θ)
              (ℚ.≤max (fst common) q))))
    ∙ sym (boundedReciprocal-rat θ (ℚ.max (fst common) q))
    ∙ sym (cong (boundedReciprocalℝ θ) (positiveClamp-rat common q))
    where
    common : ℚ₊
    common = commonReciprocalLowerBound η θ

    commonAtQ : ℚ₊
    commonAtQ = clampedPositive common q


boundedReciprocalAgreeAboveCommon : ∀ η θ x →
  boundedReciprocalℝ η
    (positiveClamp (commonReciprocalLowerBound η θ) x)
  ≡
  boundedReciprocalℝ θ
    (positiveClamp (commonReciprocalLowerBound η θ) x)
boundedReciprocalAgreeAboveCommon η θ =
  funExt⁻
    (continuousExtensionality
      (boundedReciprocalAfterClamp
        η (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterClamp
        θ (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterClampIsContinuous
        η (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterClampIsContinuous
        θ (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterClamp-rat η θ))


boundedReciprocalCompatible : ∀ η θ x →
  rat (fst η) ≤ℝ x →
  rat (fst θ) ≤ℝ x →
  boundedReciprocalℝ η x ≡ boundedReciprocalℝ θ x
boundedReciprocalCompatible η θ x η≤x θ≤x =
    sym (cong (boundedReciprocalℝ η) commonMaxFix)
  ∙ boundedReciprocalAgreeAboveCommon η θ x
  ∙ cong (boundedReciprocalℝ θ) commonMaxFix
  where
  common : ℚ₊
  common = commonReciprocalLowerBound η θ

  common≤x : rat (fst common) ≤ℝ x
  common≤x =
    subst (_≤ℝ x)
      (max-rat (fst η) (fst θ))
      (maxLeastUpperBound
        (rat (fst η)) (rat (fst θ)) x η≤x θ≤x)

  commonMaxFix : positiveClamp common x ≡ x
  commonMaxFix = common≤x
