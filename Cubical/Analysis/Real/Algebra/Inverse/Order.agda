module Cubical.Analysis.Real.Algebra.Inverse.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded
open import Cubical.Analysis.Real.Algebra.Inverse.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing


absAfterBoundedReciprocalIsLipschitz : ∀ η →
  IsLipschitzWith
    (ℝPremetricSpace .snd)
    (absℝ ∘ boundedReciprocalℝ η)
    (ℝPremetricSpace .snd)
    (reciprocalLipschitzBound η)
absAfterBoundedReciprocalIsLipschitz η
  .IsLipschitzWith.pres≈ x y ε x∼y =
    abs-pres∼
      (boundedReciprocalℝ η x) (boundedReciprocalℝ η y)
      (reciprocalLipschitzBound η ·₊ ε)
      (boundedReciprocalIsLipschitz η
        .IsLipschitzWith.pres≈ x y ε x∼y)


private
  boundedReciprocalIsContinuous : ∀ η →
    isContinuous
      (ℝPremetricSpace .snd) (boundedReciprocalℝ η)
      (ℝPremetricSpace .snd)
  boundedReciprocalIsContinuous η =
    isLipschitz→isContinuous
      (ℝPremetricSpace .snd) (boundedReciprocalℝ η)
      (ℝPremetricSpace .snd)
      ∣ reciprocalLipschitzBound η ,
        boundedReciprocalIsLipschitz η ∣₁

  absAfterBoundedReciprocalIsContinuous : ∀ η →
    isContinuous
      (ℝPremetricSpace .snd)
      (absℝ ∘ boundedReciprocalℝ η)
      (ℝPremetricSpace .snd)
  absAfterBoundedReciprocalIsContinuous η =
    isLipschitz→isContinuous
      (ℝPremetricSpace .snd)
      (absℝ ∘ boundedReciprocalℝ η)
      (ℝPremetricSpace .snd)
      ∣ reciprocalLipschitzBound η ,
        absAfterBoundedReciprocalIsLipschitz η ∣₁

  absAfterBoundedReciprocal-rat : ∀ η q →
    absℝ (boundedReciprocalℝ η (rat q)) ≡
    boundedReciprocalℝ η (rat q)
  absAfterBoundedReciprocal-rat η q =
      cong absℝ (boundedReciprocal-rat η q)
    ∙ abs-rat (boundedReciprocalℚ η q)
    ∙ cong rat
        (0≤→abs≡id
          (boundedReciprocalℚ η q)
          (ℚ.0≤ℚ₊ ((clampedPositive η q) ⁻¹₊)))
    ∙ sym (boundedReciprocal-rat η q)


boundedReciprocalAbsoluteValue : ∀ η →
  (absℝ ∘ boundedReciprocalℝ η) ≡ boundedReciprocalℝ η
boundedReciprocalAbsoluteValue η =
  continuousExtensionality
    (absℝ ∘ boundedReciprocalℝ η)
    (boundedReciprocalℝ η)
    (absAfterBoundedReciprocalIsContinuous η)
    (boundedReciprocalIsContinuous η)
    (absAfterBoundedReciprocal-rat η)


boundedReciprocalIsNonnegative : ∀ η x →
  IsNonnegative (boundedReciprocalℝ η x)
boundedReciprocalIsNonnegative η x =
  funExt⁻ (boundedReciprocalAbsoluteValue η) x


boundedReciprocalNonnegative : ∀ η x →
  0ℝ ≤ℝ boundedReciprocalℝ η x
boundedReciprocalNonnegative η x =
  isNonnegative→0≤
    (boundedReciprocalℝ η x)
    (boundedReciprocalIsNonnegative η x)


private
  ≤ℚ→≤ℝ : ∀ p q → p ℚ.≤ q → rat p ≤ℝ rat q
  ≤ℚ→≤ℝ p q = invEq (rat≤rat≃ p q)


positiveReciprocalPositiveAtBounds : ∀ x
  (p : 0ℝ <ℝ x)
  (w : PositiveGap 0ℝ x) →
  NaturalAbsBound x →
  0ℝ <ℝ positiveReciprocal x p
positiveReciprocalPositiveAtBounds
  x p w@(η , _) (n , absx<N) =
    subst (0ℝ <ℝ_)
      (sym positiveReciprocalPath)
      (<≤ℝ-trans
        0ℝ (rat (fst N⁻¹)) reciprocal
        (<ℚ→<ℝ 0 (fst N⁻¹) (snd N⁻¹))
        inverseNatural≤reciprocal)
  where
  N : ℚ₊
  N = naturalBound n

  N⁻¹ : ℚ₊
  N⁻¹ = N ⁻¹₊

  reciprocal : ℝ
  reciprocal = boundedReciprocalℝ η x

  x<N : x <ℝ rat (fst N)
  x<N = ≤<ℝ-trans x (absℝ x) (rat (fst N))
    (leAbs x) absx<N

  x≤N : x ≤ℝ rat (fst N)
  x≤N = <ℝ-weaken x (rat (fst N)) x<N

  zero≤reciprocal : 0ℝ ≤ℝ reciprocal
  zero≤reciprocal = boundedReciprocalNonnegative η x

  one≤N·reciprocal :
    1ℝ ≤ℝ rat (fst N) · reciprocal
  one≤N·reciprocal =
    subst (_≤ℝ (rat (fst N) · reciprocal))
      (boundedReciprocalLaw η x (gapLowerBound w))
      (mulPres≤R-0≤
        x (rat (fst N)) reciprocal
        zero≤reciprocal x≤N)

  zero≤inverseNatural : 0ℝ ≤ℝ rat (fst N⁻¹)
  zero≤inverseNatural =
    ≤ℚ→≤ℝ 0 (fst N⁻¹)
      (ℚ.<Weaken≤ 0 (fst N⁻¹) (snd N⁻¹))

  scaledInequality :
    1ℝ · rat (fst N⁻¹) ≤ℝ
    (rat (fst N) · reciprocal) · rat (fst N⁻¹)
  scaledInequality =
    mulPres≤R-0≤
      1ℝ (rat (fst N) · reciprocal)
      (rat (fst N⁻¹))
      zero≤inverseNatural one≤N·reciprocal

  rightPath :
    (rat (fst N) · reciprocal) · rat (fst N⁻¹) ≡
    reciprocal
  rightPath =
      sym (mulAssoc
        (rat (fst N)) reciprocal (rat (fst N⁻¹)))
    ∙ cong (rat (fst N) ·_)
        (mulComm reciprocal (rat (fst N⁻¹)))
    ∙ mulAssoc
        (rat (fst N)) (rat (fst N⁻¹)) reciprocal
    ∙ cong (_· reciprocal)
        (mul-rat (fst N) (fst N⁻¹)
        ∙ cong rat (ℚInv.x·invℚ₊[x] N))
    ∙ mulIdL reciprocal

  inverseNatural≤reciprocal :
    rat (fst N⁻¹) ≤ℝ reciprocal
  inverseNatural≤reciprocal =
    subst2 _≤ℝ_
      (mulIdL (rat (fst N⁻¹)))
      rightPath scaledInequality

  positiveReciprocalPath :
    positiveReciprocal x p ≡ reciprocal
  positiveReciprocalPath =
      cong (positiveReciprocal x)
        (isProp<ℝ 0ℝ x p ∣ w ∣₁)
    ∙ positiveReciprocalAtGap x w


positiveReciprocalPositive : ∀ x
  (p : 0ℝ <ℝ x) →
  0ℝ <ℝ positiveReciprocal x p
positiveReciprocalPositive x p =
  PT.rec
    (isProp<ℝ 0ℝ (positiveReciprocal x p))
    (λ (w : PositiveGap 0ℝ x) →
      PT.rec
        (isProp<ℝ 0ℝ (positiveReciprocal x p))
        (positiveReciprocalPositiveAtBounds x p w)
        (∃naturalAbsBound x))
    p
