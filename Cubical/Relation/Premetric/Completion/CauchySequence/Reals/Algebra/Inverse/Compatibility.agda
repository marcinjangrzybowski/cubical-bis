module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Compatibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Extensionality
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (maxRational-pres≈₁)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Bounded

open PositiveRationals


commonReciprocalLowerBound : ℚ₊ → ℚ₊ → ℚ₊
commonReciprocalLowerBound η θ = clampedPositive η (fst θ)


positiveClamp : ℚ₊ → Real.ℝ → Real.ℝ
positiveClamp η x = Real.ιℚ (fst η) ⊔ℝ x


positiveClamp-ι : ∀ η q →
  positiveClamp η (Real.ιℚ q) ≡
  Real.ιℚ (ℚ.max (fst η) q)
positiveClamp-ι η q = max-ι (fst η) q


positiveClampIsNonExpanding : ∀ η →
  IsNonExpanding
    (Real.ℝPremetricSpace .snd) (positiveClamp η)
    (Real.ℝPremetricSpace .snd)
positiveClampIsNonExpanding η
  .IsNonExpanding.pres≈ x y ε x∼y =
    subst2 (Real.Base._≈ᶜ[ ε ]_)
      (max-comm x (Real.ιℚ (fst η)))
      (max-comm y (Real.ιℚ (fst η)))
      (maxRational-pres≈₁ (fst η) x y ε x∼y)


positiveClamp-seqWitness : ∀ η {x} →
  Real.Base.IsCauchySequence x →
  Real.Base.IsCauchySequence (positiveClamp η ∘ x)
positiveClamp-seqWitness η gx =
  max-diagonalIsCauchySequence
    (constantIsCauchySequence (Real.ιℚ (fst η))) gx


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x)
    (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


positiveClamp-lim : ∀ η x gx →
  positiveClamp η (Real.Base.lim x gx) ≡
  Real.Base.lim (positiveClamp η ∘ x)
    (positiveClamp-seqWitness η gx)
positiveClamp-lim η x gx =
    max-comm (Real.ιℚ (fst η)) (Real.Base.lim x gx)
  ∙ max-lim-left x gx (Real.ιℚ (fst η))
  ∙ lim-cong _ (positiveClamp-seqWitness η gx)
      (funExt (λ n → max-comm (x n) (Real.ιℚ (fst η))))


private
  boundedReciprocalAfterClamp : ℚ₊ → ℚ₊ → Real.ℝ → Real.ℝ
  boundedReciprocalAfterClamp η common x =
    boundedReciprocalℝ η (positiveClamp common x)

  boundedReciprocalAfterClampIsLipschitz : ∀ η common →
    IsLipschitzWith
      (Real.ℝPremetricSpace .snd)
      (boundedReciprocalAfterClamp η common)
      (Real.ℝPremetricSpace .snd)
      (reciprocalLipschitzBound η)
  boundedReciprocalAfterClampIsLipschitz η common
    .IsLipschitzWith.pres≈ x y ε x∼y =
      boundedReciprocalIsLipschitz η .IsLipschitzWith.pres≈
        (positiveClamp common x) (positiveClamp common y) ε
        (positiveClampIsNonExpanding common
          .IsNonExpanding.pres≈ x y ε x∼y)

  commonContainsLeft : ∀ η θ →
    fst η ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsLeft η θ = ℚ.≤max (fst η) (fst θ)

  commonContainsRight : ∀ η θ →
    fst θ ℚ.≤ fst (commonReciprocalLowerBound η θ)
  commonContainsRight η θ = ℚ.≤max' (fst η) (fst θ)

  boundedReciprocalAfterClamp-ι : ∀ η θ q →
    boundedReciprocalAfterClamp
      η (commonReciprocalLowerBound η θ) (Real.ιℚ q)
    ≡
    boundedReciprocalAfterClamp
      θ (commonReciprocalLowerBound η θ) (Real.ιℚ q)
  boundedReciprocalAfterClamp-ι η θ q =
      cong (boundedReciprocalℝ η) (positiveClamp-ι common q)
    ∙ boundedReciprocal-ι η (ℚ.max (fst common) q)
    ∙ cong Real.ιℚ
        (boundedReciprocalℚAbove
          η (ℚ.max (fst common) q)
          (snd commonAtQ)
          (ℚ.isTrans≤
            (fst η) (fst common) (ℚ.max (fst common) q)
            (commonContainsLeft η θ)
            (ℚ.≤max (fst common) q)))
    ∙ sym
        (cong Real.ιℚ
          (boundedReciprocalℚAbove
            θ (ℚ.max (fst common) q)
            (snd commonAtQ)
            (ℚ.isTrans≤
              (fst θ) (fst common) (ℚ.max (fst common) q)
              (commonContainsRight η θ)
              (ℚ.≤max (fst common) q))))
    ∙ sym (boundedReciprocal-ι θ (ℚ.max (fst common) q))
    ∙ sym (cong (boundedReciprocalℝ θ) (positiveClamp-ι common q))
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
    (lipschitzExtensionality
      Real.ℝPremetricSpace
      (boundedReciprocalAfterClamp
        η (commonReciprocalLowerBound η θ))
      (boundedReciprocalAfterClamp
        θ (commonReciprocalLowerBound η θ))
      ∣ reciprocalLipschitzBound η ,
        boundedReciprocalAfterClampIsLipschitz
          η (commonReciprocalLowerBound η θ) ∣₁
      ∣ reciprocalLipschitzBound θ ,
        boundedReciprocalAfterClampIsLipschitz
          θ (commonReciprocalLowerBound η θ) ∣₁
      (boundedReciprocalAfterClamp-ι η θ))


boundedReciprocalCompatible : ∀ η θ x →
  Real.ιℚ (fst η) ≤ℝ x →
  Real.ιℚ (fst θ) ≤ℝ x →
  boundedReciprocalℝ η x ≡ boundedReciprocalℝ θ x
boundedReciprocalCompatible η θ x η≤x θ≤x =
    sym (cong (boundedReciprocalℝ η) commonMaxFix)
  ∙ boundedReciprocalAgreeAboveCommon η θ x
  ∙ cong (boundedReciprocalℝ θ) commonMaxFix
  where
  common : ℚ₊
  common = commonReciprocalLowerBound η θ

  common≤x : Real.ιℚ (fst common) ≤ℝ x
  common≤x =
    subst (_≤ℝ x)
      (max-ι (fst η) (fst θ))
      (max-least
        (Real.ιℚ (fst η)) (Real.ιℚ (fst θ)) x
        η≤x θ≤x)

  commonMaxFix : positiveClamp common x ≡ x
  commonMaxFix = common≤x
