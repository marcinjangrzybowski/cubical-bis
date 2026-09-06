module Cubical.Analysis.Real.Order.Strict.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Rationals.Base as ℚBase
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
  using (module PositiveRationals)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located

open PositiveRationals using (ℚ₊)


private
  opaque
    translationDifference : ∀ x increment → (x + increment) - x ≡ increment
    translationDifference x increment =
      cong (_+ (- x)) (addComm x increment)
      ∙ sym (addAssoc increment x (- x))
      ∙ cong (increment +_) (addInvR x)
      ∙ addIdR increment


opaque
  -- A positive image gap has a positive input gap on ordered inputs.  The
  -- continuity radius is eliminated only into a proposition: no choice of
  -- moduli and no classical conversion from inequality to apartness occurs.
  continuousReflectsStrictOnOrderedInputs : (f : ℝ → ℝ) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    ∀ x y → x ≤ℝ y → f x <ℝ f y → x <ℝ y
  continuousReflectsStrictOnOrderedInputs f continuous x y x≤y =
    PT.rec (isProp<ℝ x y) fromGap
    where
    fromGap : PositiveGap (f x) (f y) → x <ℝ y
    fromGap (ε , image-gap) =
      PT.rec (isProp<ℝ x y) fromRadius
        (continuous x .IsContinuousAt.pres≈ ε)
      where
      fromRadius :
        (Σ[ δ ∈ ℚ₊ ] (∀ z → x ∼[ δ ] z → f x ∼[ ε ] f z)) →
        x <ℝ y
      fromRadius (δ , preserves) =
        PT.rec (isProp<ℝ x y) (⊎.rec nearbyImpossible (λ ordered → ordered))
          (dichotomyℝ x y (x + rat (fst δ))
            (subst (_<ℝ x + rat (fst δ)) (addIdR x)
              (<ℝ-addL 0ℝ (rat (fst δ)) x
                (<ℚ→<ℝ 0 (fst δ) (snd δ)))))
        where
        nearbyImpossible : y <ℝ x + rat (fst δ) → x <ℝ y
        nearbyImpossible nearby = ⊥.rec
          (≤ℝ→≯ (rat (fst ε)) (f y - f x) gapBound closeBound)
          where
          inputClose : x ∼[ δ ] y
          inputClose =
            sym∼ y x δ
              (absDifference<→closeness y x δ
                (subst (_<ℝ rat (fst δ))
                  (sym (absOfNonnegative (y - x) (nonnegativeSub x y x≤y)))
                  (subst ((y - x) <ℝ_) (translationDifference x (rat (fst δ)))
                    (<ℝ-addR y (x + rat (fst δ)) (- x) nearby))))

          gapBound : rat (fst ε) ≤ℝ f y - f x
          gapBound =
            subst (_≤ℝ (f y - f x)) (translationDifference (f x) (rat (fst ε)))
              (addPres≤R (f x + rat (fst ε)) (f y) (- f x) image-gap)

          closeBound : f y - f x <ℝ rat (fst ε)
          closeBound =
            ≤<ℝ-trans (f y - f x) (absℝ (f y - f x)) (rat (fst ε))
              (leAbs (f y - f x))
              (closeness→absDifference< (f y) (f x) ε
                (sym∼ (f x) (f y) ε (preserves y inputClose)))
