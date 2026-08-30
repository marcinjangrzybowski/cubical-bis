module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Extensionality
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Bounded
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive

open PositiveRationals

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


opaque
  absAfterBoundedReciprocalIsLipschitz : ∀ η →
    IsLipschitzWith
      (Real.ℝPremetricSpace .snd)
      (Abs.absℝ ∘ boundedReciprocalℝ η)
      (Real.ℝPremetricSpace .snd)
      (reciprocalLipschitzBound η)
  absAfterBoundedReciprocalIsLipschitz η
    .IsLipschitzWith.pres≈ x y ε x∼y =
      Abs.absℝ-pres≈
        (boundedReciprocalℝ η x) (boundedReciprocalℝ η y)
        (reciprocalLipschitzBound η ·₊ ε)
        (boundedReciprocalIsLipschitz η
          .IsLipschitzWith.pres≈ x y ε x∼y)

  absAfterBoundedReciprocal-ι : ∀ η q →
    Abs.absℝ (boundedReciprocalℝ η (Real.ιℚ q)) ≡
    boundedReciprocalℝ η (Real.ιℚ q)
  absAfterBoundedReciprocal-ι η q =
      cong Abs.absℝ (boundedReciprocal-ι η q)
    ∙ Abs.absℝ-ι (boundedReciprocalℚ η q)
    ∙ cong Real.ιℚ
        (ℚOrder.0≤→abs≡id
          (boundedReciprocalℚ η q)
          (ℚ.0≤ℚ₊ ((clampedPositive η q) ⁻¹₊)))
    ∙ sym (boundedReciprocal-ι η q)

  boundedReciprocalAbsoluteValue : ∀ η →
    (Abs.absℝ ∘ boundedReciprocalℝ η) ≡ boundedReciprocalℝ η
  boundedReciprocalAbsoluteValue η =
    lipschitzExtensionality
      Real.ℝPremetricSpace
      (Abs.absℝ ∘ boundedReciprocalℝ η)
      (boundedReciprocalℝ η)
      ∣ reciprocalLipschitzBound η ,
        absAfterBoundedReciprocalIsLipschitz η ∣₁
      ∣ reciprocalLipschitzBound η ,
        boundedReciprocalIsLipschitz η ∣₁
      (absAfterBoundedReciprocal-ι η)

  boundedReciprocalNonnegative : ∀ η x →
    Real.ιℚ 0 ≤ℝ boundedReciprocalℝ η x
  boundedReciprocalNonnegative η x =
    abs-self→nonnegative (boundedReciprocalℝ η x)
      (funExt⁻ (boundedReciprocalAbsoluteValue η) x)


opaque
  positiveReciprocalPositiveAtBounds : ∀ x
    (p : Real.ιℚ 0 <ℝ x)
    (w : PositiveGap (Real.ιℚ 0) x) →
    NaturalBound x →
    Real.ιℚ 0 <ℝ positiveReciprocal x p
  positiveReciprocalPositiveAtBounds x p w (n , absx<N) =
    subst (Real.ιℚ 0 <ℝ_)
      (sym positiveReciprocalPath)
      (≪≤ℝ-trans
        (Real.ιℚ 0) (Real.ιℚ (fst N⁻¹)) reciprocal
        (<ℚ→<ℝ 0 (fst N⁻¹) (snd N⁻¹))
        inverseNatural≤reciprocal)
    where
    η : ℚ₊
    η = width w

    N : ℚ₊
    N = naturalRational n , naturalPositive n

    N⁻¹ : ℚ₊
    N⁻¹ = N ⁻¹₊

    reciprocal : Real.ℝ
    reciprocal = boundedReciprocalℝ η x

    x<N : x <ℝ Real.ιℚ (fst N)
    x<N = ≤<ℝ-trans x (Abs.absℝ x) (Real.ιℚ (fst N))
      (x≤abs x) absx<N

    x≤N : x ≤ℝ Real.ιℚ (fst N)
    x≤N = <ℝ-weaken x (Real.ιℚ (fst N)) x<N

    zero≤reciprocal : Real.ιℚ 0 ≤ℝ reciprocal
    zero≤reciprocal = boundedReciprocalNonnegative η x

    one≤N·reciprocal :
      Real.ιℚ 1 ≤ℝ Real.ιℚ (fst N) Mul.· reciprocal
    one≤N·reciprocal =
      subst (_≤ℝ (Real.ιℚ (fst N) Mul.· reciprocal))
        (boundedReciprocalLaw η x (gapLowerBound w))
        (mul-preserves≤-right-nonnegative
          x (Real.ιℚ (fst N)) reciprocal
          x≤N zero≤reciprocal)

    zero≤inverseNatural : Real.ιℚ 0 ≤ℝ Real.ιℚ (fst N⁻¹)
    zero≤inverseNatural =
      ≤ℚ→≤ℝ 0 (fst N⁻¹)
        (ℚ.<Weaken≤ 0 (fst N⁻¹) (snd N⁻¹))

    scaledInequality :
      Real.ιℚ 1 Mul.· Real.ιℚ (fst N⁻¹) ≤ℝ
      (Real.ιℚ (fst N) Mul.· reciprocal) Mul.·
        Real.ιℚ (fst N⁻¹)
    scaledInequality =
      mul-preserves≤-right-nonnegative
        (Real.ιℚ 1)
        (Real.ιℚ (fst N) Mul.· reciprocal)
        (Real.ιℚ (fst N⁻¹))
        one≤N·reciprocal zero≤inverseNatural

    rightPath :
      (Real.ιℚ (fst N) Mul.· reciprocal) Mul.·
        Real.ιℚ (fst N⁻¹) ≡ reciprocal
    rightPath =
        sym (mul-assoc
          (Real.ιℚ (fst N)) reciprocal (Real.ιℚ (fst N⁻¹)))
      ∙ cong (Real.ιℚ (fst N) Mul.·_)
          (mul-comm reciprocal (Real.ιℚ (fst N⁻¹)))
      ∙ mul-assoc
          (Real.ιℚ (fst N)) (Real.ιℚ (fst N⁻¹)) reciprocal
      ∙ cong (Mul._· reciprocal)
          (Mul.mul-ι-ι (fst N) (fst N⁻¹)
          ∙ cong Real.ιℚ (ℚInv.x·invℚ₊[x] N))
      ∙ mul-one-left reciprocal

    inverseNatural≤reciprocal :
      Real.ιℚ (fst N⁻¹) ≤ℝ reciprocal
    inverseNatural≤reciprocal =
      subst2 _≤ℝ_
        (mul-one-left (Real.ιℚ (fst N⁻¹)))
        rightPath scaledInequality

    positiveReciprocalPath :
      positiveReciprocal x p ≡ reciprocal
    positiveReciprocalPath =
      cong (positiveReciprocal x)
        (isProp<ℝ (Real.ιℚ 0) x p ∣ w ∣₁)
      ∙ positiveReciprocalAtGap x w


positiveReciprocalPositive : ∀ x
  (p : Real.ιℚ 0 <ℝ x) →
  Real.ιℚ 0 <ℝ positiveReciprocal x p
positiveReciprocalPositive x p =
  PT.rec
    (isProp<ℝ (Real.ιℚ 0) (positiveReciprocal x p))
    (λ w →
      PT.rec
        (isProp<ℝ (Real.ιℚ 0) (positiveReciprocal x p))
        (positiveReciprocalPositiveAtBounds x p w)
        (∃naturalBound x))
    p
