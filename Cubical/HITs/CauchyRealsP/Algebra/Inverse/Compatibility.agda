module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Compatibility where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Bounded

open import Cubical.Relation.Premetric.Mappings

commonReciprocalLowerBound : ℚ₊ → ℚ₊ → ℚ₊
commonReciprocalLowerBound η θ =
  clampedPositive η (fst θ)

private
  boundedReciprocalAfterCommonMax : ℚ₊ → ℚ₊ → ℚ₊ → ℝ → ℝ
  boundedReciprocalAfterCommonMax η θ common x =
    boundedReciprocalℝ η (maxℝ (rat (fst common)) x)

  boundedReciprocalAfterCommonMaxLip : ∀ η θ common →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (boundedReciprocalAfterCommonMax η θ common)
      (snd ℝPremetricSpace)
      (reciprocalLipschitzBound η)
  boundedReciprocalAfterCommonMaxLip η θ common
    .IsLipschitzWith.pres≈ x y ε x∼y =
      IsLipschitzWith.pres≈
        (boundedReciprocalIsLipschitz η)
        (maxℝ (rat (fst common)) x)
        (maxℝ (rat (fst common)) y)
        ε
        (maxPres∼₂
          (rat (fst common)) x y ε x∼y)

  commonContainsLeft : ∀ η θ →
    fst η ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsLeft η θ =
    ℚ.≤max (fst η) (fst θ)

  commonContainsRight : ∀ η θ →
    fst θ ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsRight η θ =
    ℚ.≤max' (fst η) (fst θ)

  boundedReciprocalAfterCommonMax-rat : ∀ η θ q →
    boundedReciprocalAfterCommonMax
      η θ (commonReciprocalLowerBound η θ) (rat q)
    ≡
    boundedReciprocalAfterCommonMax
      θ η (commonReciprocalLowerBound η θ) (rat q)
  boundedReciprocalAfterCommonMax-rat η θ q =
    cong (boundedReciprocalℝ η)
      (max-rat (fst common) q)
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
    ∙ sym
        (boundedReciprocal-rat θ (ℚ.max (fst common) q))
    ∙ sym
        (cong (boundedReciprocalℝ θ)
          (max-rat (fst common) q))
    where
    common : ℚ₊
    common =
      commonReciprocalLowerBound η θ

    commonAtQ : ℚ₊
    commonAtQ =
      clampedPositive common q

boundedReciprocalAgreeAboveCommon : ∀ η θ x →
  boundedReciprocalℝ η
    (maxℝ
      (rat (fst (commonReciprocalLowerBound η θ))) x)
  ≡
  boundedReciprocalℝ θ
    (maxℝ
      (rat (fst (commonReciprocalLowerBound η θ))) x)
boundedReciprocalAgreeAboveCommon η θ =
  funExt⁻
    (lipschitzExtensionality
      ℝPremetricSpace
      (boundedReciprocalAfterCommonMax
        η θ (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterCommonMax
        θ η (commonReciprocalLowerBound η θ))
      ∣ reciprocalLipschitzBound η ,
        boundedReciprocalAfterCommonMaxLip
          η θ (commonReciprocalLowerBound η θ) ∣₁
      ∣ reciprocalLipschitzBound θ ,
        boundedReciprocalAfterCommonMaxLip
          θ η (commonReciprocalLowerBound η θ) ∣₁
      (boundedReciprocalAfterCommonMax-rat η θ))

boundedReciprocalCompatible : ∀ η θ x →
  rat (fst η) ≤ℝ x →
  rat (fst θ) ≤ℝ x →
  boundedReciprocalℝ η x ≡ boundedReciprocalℝ θ x
boundedReciprocalCompatible η θ x η≤x θ≤x =
  sym
    (cong (boundedReciprocalℝ η) commonMaxFix)
  ∙ boundedReciprocalAgreeAboveCommon η θ x
  ∙ cong (boundedReciprocalℝ θ) commonMaxFix
  where
  common : ℚ₊
  common =
    commonReciprocalLowerBound η θ

  common≤x : rat (fst common) ≤ℝ x
  common≤x =
    subst (_≤ℝ x)
      (max-rat (fst η) (fst θ))
      (max≤
        (rat (fst η)) (rat (fst θ)) x
        η≤x θ≤x)

  commonMaxFix :
    maxℝ (rat (fst common)) x ≡ x
  commonMaxFix =
    maxOf≤ (rat (fst common)) x common≤x
