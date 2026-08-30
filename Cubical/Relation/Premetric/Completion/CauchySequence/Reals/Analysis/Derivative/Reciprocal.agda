module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Reciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (close→lowerBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Bounded
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- This is the quantitative core of reciprocal differentiation.  Retaining
-- the positive rational lower bound in the domain gives a globally
-- Lipschitz reciprocal and an untruncated, reusable bound.  Later local
-- reciprocal rules can open a merely existing gap only while selecting one
-- of these domains.

LowerBoundedPositivePredicate :
  ℚ₊ → ℙ Real.ℝ
LowerBoundedPositivePredicate η x =
  (Real.ιℚ (fst η) ≤ℝ x)
  , isProp≤ℝ (Real.ιℚ (fst η)) x


LowerBoundedPositive :
  ℚ₊ → Type₀
LowerBoundedPositive η =
  Σ[ x ∈ Real.ℝ ]
    x ∈ LowerBoundedPositivePredicate η


LowerBoundedPositivePremetricSpace :
  ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
LowerBoundedPositivePremetricSpace η =
  PremetricSubspace Real.ℝPremetricSpace
    (LowerBoundedPositivePredicate η)


lowerBoundedPositiveCoordinate :
  ∀ η → LowerBoundedPositive η → Real.ℝ
lowerBoundedPositiveCoordinate η = fst


lowerBoundedPositiveReciprocal :
  ∀ η → LowerBoundedPositive η → Real.ℝ
lowerBoundedPositiveReciprocal η point =
  boundedReciprocalℝ η (fst point)


lowerBoundedPositiveReciprocalDerivative :
  ∀ η → LowerBoundedPositive η → Real.ℝ
lowerBoundedPositiveReciprocalDerivative η point =
  Neg.-
    (lowerBoundedPositiveReciprocal η point Mul.·
      lowerBoundedPositiveReciprocal η point)


lowerBoundedPositiveCoordinateIsContinuous :
  ∀ η →
  isContinuous
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (snd Real.ℝPremetricSpace)
lowerBoundedPositiveCoordinateIsContinuous η =
  snd
    (NE→C
      (subspaceInclusionNE
        Real.ℝPremetricSpace
        (LowerBoundedPositivePredicate η)))


boundedReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (snd Real.ℝPremetricSpace)
    (boundedReciprocalℝ η)
    (snd Real.ℝPremetricSpace)
boundedReciprocalIsContinuous η =
  isLipschitz→isContinuous
    (snd Real.ℝPremetricSpace)
    (boundedReciprocalℝ η)
    (snd Real.ℝPremetricSpace)
    ∣ reciprocalLipschitzBound η
      , boundedReciprocalIsLipschitz η ∣₁


lowerBoundedPositiveReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveReciprocal η)
    (snd Real.ℝPremetricSpace)
lowerBoundedPositiveReciprocalIsContinuous η =
  snd
    (CategoryStructures._∘C_
      ( boundedReciprocalℝ η
      , boundedReciprocalIsContinuous η
      )
      ( lowerBoundedPositiveCoordinate η
      , lowerBoundedPositiveCoordinateIsContinuous η
      ))


lowerBoundedPositiveReciprocalDifferenceFactor :
  ∀ η →
  LowerBoundedPositive η
    × LowerBoundedPositive η → Real.ℝ
lowerBoundedPositiveReciprocalDifferenceFactor
  η (x , y) =
    Neg.-
      (lowerBoundedPositiveReciprocal η x Mul.·
        lowerBoundedPositiveReciprocal η y)


private
  reciprocalDifferenceFactorization :
    ∀ η (x y : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocal η y
        Group.- lowerBoundedPositiveReciprocal η x
      ≡
    (fst y Group.- fst x) Mul.·
      lowerBoundedPositiveReciprocalDifferenceFactor
        η (x , y)
  reciprocalDifferenceFactorization η x y =
    cong₂ Group._-_
      reciprocal-y-as-x-product
      reciprocal-x-as-y-product
    ∙ sym
        (ℝRing.·DistL-
          (fst x) (fst y) reciprocal-product)
    ∙ cong
        (Mul._· reciprocal-product)
        (sym (neg-sub (fst y) (fst x)))
    ∙ ℝRing.-DistL·
        (fst y Group.- fst x) reciprocal-product
    ∙ sym
        (ℝRing.-DistR·
          (fst y Group.- fst x) reciprocal-product)
    where
    reciprocal-x : Real.ℝ
    reciprocal-x = lowerBoundedPositiveReciprocal η x

    reciprocal-y : Real.ℝ
    reciprocal-y = lowerBoundedPositiveReciprocal η y

    reciprocal-product : Real.ℝ
    reciprocal-product = reciprocal-x Mul.· reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y ≡ fst x Mul.· reciprocal-product
    reciprocal-y-as-x-product =
      sym (mul-one-left reciprocal-y)
      ∙ cong
          (Mul._· reciprocal-y)
          (sym (boundedReciprocalLaw η (fst x) (snd x)))
      ∙ sym (mul-assoc (fst x) reciprocal-x reciprocal-y)

    reciprocal-x-as-y-product :
      reciprocal-x ≡ fst y Mul.· reciprocal-product
    reciprocal-x-as-y-product =
      sym (mul-one-right reciprocal-x)
      ∙ cong
          (reciprocal-x Mul.·_)
          (sym (boundedReciprocalLaw η (fst y) (snd y)))
      ∙ mul-assoc reciprocal-x (fst y) reciprocal-y
      ∙ cong
          (Mul._· reciprocal-y)
          (mul-comm reciprocal-x (fst y))
      ∙ sym (mul-assoc (fst y) reciprocal-x reciprocal-y)


  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal :
    ∀ η (x : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocalDifferenceFactor
        η (x , x)
      ≡
    lowerBoundedPositiveReciprocalDerivative η x
  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal η x =
    refl


  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous :
    ∀ η →
    isContinuous
      (PremetricProductStr
        (snd (LowerBoundedPositivePremetricSpace η))
        (snd (LowerBoundedPositivePremetricSpace η)))
      (lowerBoundedPositiveReciprocalDifferenceFactor η)
      (snd Real.ℝPremetricSpace)
  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous η =
    snd
      (CategoryStructures._∘C_
        ( Neg.-_
        , isNonExpanding→isContinuous
            (snd Real.ℝPremetricSpace)
            Neg.-_
            (snd Real.ℝPremetricSpace)
            (snd Neg.negationⁿ)
        )
        ( ( λ points →
              lowerBoundedPositiveReciprocal η (fst points) Mul.·
                lowerBoundedPositiveReciprocal η (snd points))
        , mulOfContinuousIsContinuous
            (PremetricProductStr
              (snd (LowerBoundedPositivePremetricSpace η))
              (snd (LowerBoundedPositivePremetricSpace η)))
            (lowerBoundedPositiveReciprocal η ∘ fst)
            (lowerBoundedPositiveReciprocal η ∘ snd)
            (snd
              (CategoryStructures._∘C_
                ( lowerBoundedPositiveReciprocal η
                , lowerBoundedPositiveReciprocalIsContinuous η
                )
                (productFstC
                  {M = LowerBoundedPositivePremetricSpace η}
                  {N = LowerBoundedPositivePremetricSpace η})))
            (snd
              (CategoryStructures._∘C_
                ( lowerBoundedPositiveReciprocal η
                , lowerBoundedPositiveReciprocalIsContinuous η
                )
                (productSndC
                  {M = LowerBoundedPositivePremetricSpace η}
                  {N = LowerBoundedPositivePremetricSpace η})))
        ))


lowerBoundedPositiveReciprocalHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveReciprocal η)
    (lowerBoundedPositiveReciprocalDerivative η)
lowerBoundedPositiveReciprocalHasDerivativeAlong η =
  continuousDifferenceFactorGivesDerivative
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveReciprocal η)
    (lowerBoundedPositiveReciprocalDerivative η)
    (lowerBoundedPositiveReciprocalDifferenceFactor η)
    (reciprocalDifferenceFactorization η)
    (lowerBoundedPositiveReciprocalDifferenceFactorDiagonal η)
    (lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous η)


-- On the lower-bounded domain, the generic bounded lift agrees with the
-- proof-independent positive reciprocal.  This isolates all dependence on
-- the quantitative bound in a path, so later local arguments can change
-- bounds without changing the represented function.

lowerBoundedPositiveGap :
  ∀ η (point : LowerBoundedPositive η) →
  PositiveGap (Real.ιℚ 0) (fst point)
lowerBoundedPositiveGap η point =
  positiveGap η
    (subst
      (_≤ℝ fst point)
      (sym (add-zero-left (Real.ιℚ (fst η))))
      (snd point))


lowerBoundedPositiveIsPositive :
  ∀ η (point : LowerBoundedPositive η) →
  Real.ιℚ 0 <ℝ fst point
lowerBoundedPositiveIsPositive η point =
  ∣ lowerBoundedPositiveGap η point ∣₁


positiveReciprocalOnLowerBound :
  ∀ η → LowerBoundedPositive η → Real.ℝ
positiveReciprocalOnLowerBound η point =
  positiveReciprocal
    (fst point)
    (lowerBoundedPositiveIsPositive η point)


positiveReciprocalOnLowerBoundDerivative :
  ∀ η → LowerBoundedPositive η → Real.ℝ
positiveReciprocalOnLowerBoundDerivative η point =
  Neg.-
    (positiveReciprocalOnLowerBound η point Mul.·
      positiveReciprocalOnLowerBound η point)


positiveReciprocalOnLowerBound≡bounded :
  ∀ η (point : LowerBoundedPositive η) →
  positiveReciprocalOnLowerBound η point
    ≡ lowerBoundedPositiveReciprocal η point
positiveReciprocalOnLowerBound≡bounded η point =
  cong
      (positiveReciprocal (fst point))
      (isProp<ℝ (Real.ιℚ 0) (fst point)
        (lowerBoundedPositiveIsPositive η point)
        ∣ lowerBoundedPositiveGap η point ∣₁)
  ∙ positiveReciprocalAtGap
      (fst point)
      (lowerBoundedPositiveGap η point)


positiveReciprocalOnLowerBoundHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (positiveReciprocalOnLowerBound η)
    (positiveReciprocalOnLowerBoundDerivative η)
positiveReciprocalOnLowerBoundHasDerivativeAlong η =
  subst2
    (IsDerivativeAlong
      (snd (LowerBoundedPositivePremetricSpace η))
      (lowerBoundedPositiveCoordinate η))
    (sym function-path)
    (sym derivative-path)
    (lowerBoundedPositiveReciprocalHasDerivativeAlong η)
  where
  function-path :
    positiveReciprocalOnLowerBound η
      ≡ lowerBoundedPositiveReciprocal η
  function-path =
    funExt (positiveReciprocalOnLowerBound≡bounded η)

  derivative-path :
    positiveReciprocalOnLowerBoundDerivative η
      ≡ lowerBoundedPositiveReciprocalDerivative η
  derivative-path =
    funExt λ point →
      cong Neg.-_
        (cong₂ Mul._·_
          (positiveReciprocalOnLowerBound≡bounded η point)
          (positiveReciprocalOnLowerBound≡bounded η point))


-- The full positive subspace carries no selected lower bound.  At each
-- point, however, a representative of the truncated strict gap can be
-- halved.  Nearby positive reals then share that fixed lower bound.  This
-- is enough to inherit continuity from the bounded lift, and the witness is
-- discarded again inside the proposition-valued continuity statement.

PositiveRealPredicate : ℙ Real.ℝ
PositiveRealPredicate x =
  (Real.ιℚ 0 <ℝ x)
  , isProp<ℝ (Real.ιℚ 0) x


PositiveReal : Type₀
PositiveReal =
  Σ[ x ∈ Real.ℝ ] x ∈ PositiveRealPredicate


PositiveRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
PositiveRealPremetricSpace =
  PremetricSubspace Real.ℝPremetricSpace PositiveRealPredicate


positiveRealCoordinate : PositiveReal → Real.ℝ
positiveRealCoordinate = fst


positiveRealCoordinateIsContinuous :
  isContinuous
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    (snd Real.ℝPremetricSpace)
positiveRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        Real.ℝPremetricSpace PositiveRealPredicate))


positiveRealReciprocal : PositiveReal → Real.ℝ
positiveRealReciprocal point =
  positiveReciprocal (fst point) (snd point)


positiveRealReciprocalDerivative : PositiveReal → Real.ℝ
positiveRealReciprocalDerivative point =
  Neg.-
    (positiveRealReciprocal point Mul.·
      positiveRealReciprocal point)


private
  halfGapLowerBound :
    ∀ {x} (w : PositiveGap (Real.ιℚ 0) x) →
    Real.ιℚ (fst (width w /2₊)) ≤ℝ x
  halfGapLowerBound {x} w =
    ≤ℝ-trans
      (Real.ιℚ (fst (width w /2₊)))
      (Real.ιℚ (fst (width w))) x
      (≤ℚ→≤ℝ
        (fst (width w /2₊))
        (fst (width w))
        (ℚ.<Weaken≤ _ _ (/2₊<id (width w))))
      (gapLowerBound w)


  halfGapBelowShiftedPoint :
    ∀ {x} (w : PositiveGap (Real.ιℚ 0) x) →
    Real.ιℚ (fst (width w /2₊))
      ≤ℝ x Group.- Real.ιℚ (fst (width w /2₊))
  halfGapBelowShiftedPoint {x} w =
    subst2 _≤ℝ_
      cancel-right-half
      refl
      (add-preserves≤-right
        (half Add.+ half) x (Neg.- half)
        two-halves-below-x)
    where
    half : Real.ℝ
    half = Real.ιℚ (fst (width w /2₊))

    two-halves-path :
      half Add.+ half ≡ Real.ιℚ (fst (width w))
    two-halves-path =
      Add.add-ι-ι
        (fst (width w /2₊))
        (fst (width w /2₊))
      ∙ cong Real.ιℚ
          (1/2∈ℚ./2+/2≡id (fst (width w)))

    two-halves-below-x : half Add.+ half ≤ℝ x
    two-halves-below-x =
      subst (_≤ℝ x)
        (sym two-halves-path)
        (gapLowerBound w)

    cancel-right-half :
      (half Add.+ half) Add.+ (Neg.- half) ≡ half
    cancel-right-half = add-sub-cancel half half


  nearRealPointAboveHalfGap :
    ∀ (x y : Real.ℝ)
      (w : PositiveGap (Real.ιℚ 0) x) →
    x Real.Base.≈ᶜ[ width w /2₊ ] y →
    Real.ιℚ (fst (width w /2₊)) ≤ℝ y
  nearRealPointAboveHalfGap x y w x≈y =
    ≤ℝ-trans
      (Real.ιℚ (fst (width w /2₊)))
      (x Group.- Real.ιℚ (fst (width w /2₊)))
      y
      (halfGapBelowShiftedPoint w)
      (close→lowerBound y x (width w /2₊)
        (Real.Base.sym≈ᶜ x y (width w /2₊) x≈y))


positiveGapHalfNeighbourPositive :
  ∀ (x y : Real.ℝ)
    (w : PositiveGap (Real.ιℚ 0) x) →
  x Real.Base.≈ᶜ[ width w /2₊ ] y →
  Real.ιℚ 0 <ℝ y
positiveGapHalfNeighbourPositive x y w x≈y =
  lowerBoundedPositiveIsPositive
    (width w /2₊)
    ( y
    , nearRealPointAboveHalfGap x y w x≈y
    )


positiveRealReciprocalIsContinuous :
  isContinuous
    (snd PositiveRealPremetricSpace)
    positiveRealReciprocal
    (snd Real.ℝPremetricSpace)
positiveRealReciprocalIsContinuous x
  .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ continuous-at-gap (snd x)
  where
  continuous-at-gap :
    PositiveGap (Real.ιℚ 0) (fst x) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_
          (snd PositiveRealPremetricSpace) x δ y →
        positiveRealReciprocal x
          Real.Base.≈ᶜ[ ε ] positiveRealReciprocal y)
  continuous-at-gap w =
    PT.map convert-local-continuity
      (boundedReciprocalIsContinuous half-width
        (fst x) .IsContinuousAt.pres≈ ε)
    where
    half-width : ℚ₊
    half-width = width w /2₊

    x-at-half : LowerBoundedPositive half-width
    x-at-half = fst x , halfGapLowerBound w

    x-function-path :
      positiveRealReciprocal x ≡
        boundedReciprocalℝ half-width (fst x)
    x-function-path =
      sym
        (cong (positiveReciprocal (fst x))
          (isProp<ℝ (Real.ιℚ 0) (fst x)
            (lowerBoundedPositiveIsPositive half-width x-at-half)
            (snd x)))
      ∙ positiveReciprocalOnLowerBound≡bounded
          half-width x-at-half

    convert-local-continuity :
      Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          (fst x) Real.Base.≈ᶜ[ δ ] y →
          boundedReciprocalℝ half-width (fst x)
            Real.Base.≈ᶜ[ ε ]
          boundedReciprocalℝ half-width y)
      →
      Σ[ κ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd PositiveRealPremetricSpace) x κ y →
          positiveRealReciprocal x
            Real.Base.≈ᶜ[ ε ] positiveRealReciprocal y)
    convert-local-continuity (δ , bounded-continuity) =
      min₊ δ half-width
      , λ y x≈y →
          let
            x≈δy : fst x Real.Base.≈ᶜ[ δ ] fst y
            x≈δy =
              PremetricStr.isMonotone≈≤
                (snd PositiveRealPremetricSpace)
                x y (min₊ δ half-width) δ
                (min₊≤L δ half-width) x≈y

            x≈halfy :
              fst x Real.Base.≈ᶜ[ half-width ] fst y
            x≈halfy =
              PremetricStr.isMonotone≈≤
                (snd PositiveRealPremetricSpace)
                x y (min₊ δ half-width) half-width
                (min₊≤R δ half-width) x≈y

            y-at-half : LowerBoundedPositive half-width
            y-at-half =
              fst y
              , nearRealPointAboveHalfGap
                  (fst x) (fst y) w x≈halfy

            y-function-path :
              positiveRealReciprocal y ≡
                boundedReciprocalℝ half-width (fst y)
            y-function-path =
              sym
                (cong (positiveReciprocal (fst y))
                  (isProp<ℝ (Real.ιℚ 0) (fst y)
                    (lowerBoundedPositiveIsPositive
                      half-width y-at-half)
                    (snd y)))
              ∙ positiveReciprocalOnLowerBound≡bounded
                  half-width y-at-half
          in
          subst2 (Real.Base._≈ᶜ[ ε ]_)
            (sym x-function-path)
            (sym y-function-path)
            (bounded-continuity (fst y) x≈δy)


positiveRealReciprocalDifferenceFactor :
  PositiveReal × PositiveReal → Real.ℝ
positiveRealReciprocalDifferenceFactor (x , y) =
  Neg.-
    (positiveRealReciprocal x Mul.·
      positiveRealReciprocal y)


private
  positiveRealReciprocalDifferenceFactorization :
    ∀ (x y : PositiveReal) →
    positiveRealReciprocal y Group.- positiveRealReciprocal x
      ≡
    (fst y Group.- fst x) Mul.·
      positiveRealReciprocalDifferenceFactor (x , y)
  positiveRealReciprocalDifferenceFactorization x y =
    cong₂ Group._-_
      reciprocal-y-as-x-product
      reciprocal-x-as-y-product
    ∙ sym
        (ℝRing.·DistL-
          (fst x) (fst y) reciprocal-product)
    ∙ cong
        (Mul._· reciprocal-product)
        (sym (neg-sub (fst y) (fst x)))
    ∙ ℝRing.-DistL·
        (fst y Group.- fst x) reciprocal-product
    ∙ sym
        (ℝRing.-DistR·
          (fst y Group.- fst x) reciprocal-product)
    where
    reciprocal-x : Real.ℝ
    reciprocal-x = positiveRealReciprocal x

    reciprocal-y : Real.ℝ
    reciprocal-y = positiveRealReciprocal y

    reciprocal-product : Real.ℝ
    reciprocal-product = reciprocal-x Mul.· reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y ≡ fst x Mul.· reciprocal-product
    reciprocal-y-as-x-product =
      sym (mul-one-left reciprocal-y)
      ∙ cong
          (Mul._· reciprocal-y)
          (sym (positiveReciprocalLaw (fst x) (snd x)))
      ∙ sym (mul-assoc (fst x) reciprocal-x reciprocal-y)

    reciprocal-x-as-y-product :
      reciprocal-x ≡ fst y Mul.· reciprocal-product
    reciprocal-x-as-y-product =
      sym (mul-one-right reciprocal-x)
      ∙ cong
          (reciprocal-x Mul.·_)
          (sym (positiveReciprocalLaw (fst y) (snd y)))
      ∙ mul-assoc reciprocal-x (fst y) reciprocal-y
      ∙ cong
          (Mul._· reciprocal-y)
          (mul-comm reciprocal-x (fst y))
      ∙ sym (mul-assoc (fst y) reciprocal-x reciprocal-y)


  positiveRealReciprocalDifferenceFactorDiagonal :
    ∀ x →
    positiveRealReciprocalDifferenceFactor (x , x)
      ≡ positiveRealReciprocalDerivative x
  positiveRealReciprocalDifferenceFactorDiagonal x = refl


  positiveRealReciprocalDifferenceFactorIsContinuous :
    isContinuous
      (PremetricProductStr
        (snd PositiveRealPremetricSpace)
        (snd PositiveRealPremetricSpace))
      positiveRealReciprocalDifferenceFactor
      (snd Real.ℝPremetricSpace)
  positiveRealReciprocalDifferenceFactorIsContinuous =
    snd
      (CategoryStructures._∘C_
        ( Neg.-_
        , isNonExpanding→isContinuous
            (snd Real.ℝPremetricSpace)
            Neg.-_
            (snd Real.ℝPremetricSpace)
            (snd Neg.negationⁿ)
        )
        ( ( λ points →
              positiveRealReciprocal (fst points) Mul.·
                positiveRealReciprocal (snd points))
        , mulOfContinuousIsContinuous
            (PremetricProductStr
              (snd PositiveRealPremetricSpace)
              (snd PositiveRealPremetricSpace))
            (positiveRealReciprocal ∘ fst)
            (positiveRealReciprocal ∘ snd)
            (snd
              (CategoryStructures._∘C_
                ( positiveRealReciprocal
                , positiveRealReciprocalIsContinuous
                )
                (productFstC
                  {M = PositiveRealPremetricSpace}
                  {N = PositiveRealPremetricSpace})))
            (snd
              (CategoryStructures._∘C_
                ( positiveRealReciprocal
                , positiveRealReciprocalIsContinuous
                )
                (productSndC
                  {M = PositiveRealPremetricSpace}
                  {N = PositiveRealPremetricSpace})))
        ))


positiveRealReciprocalHasDerivativeAlong :
  IsDerivativeAlong
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    positiveRealReciprocal
    positiveRealReciprocalDerivative
positiveRealReciprocalHasDerivativeAlong =
  continuousDifferenceFactorGivesDerivative
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    positiveRealReciprocal
    positiveRealReciprocalDerivative
    positiveRealReciprocalDifferenceFactor
    positiveRealReciprocalDifferenceFactorization
    positiveRealReciprocalDifferenceFactorDiagonal
    positiveRealReciprocalDifferenceFactorIsContinuous


-- Negative reciprocals are obtained by a nonexpanding negation pullback,
-- not by repeating the local lower-bound argument.

NegativeRealPredicate : ℙ Real.ℝ
NegativeRealPredicate x =
  (x <ℝ Real.ιℚ 0)
  , isProp<ℝ x (Real.ιℚ 0)


NegativeReal : Type₀
NegativeReal =
  Σ[ x ∈ Real.ℝ ] x ∈ NegativeRealPredicate


NegativeRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
NegativeRealPremetricSpace =
  PremetricSubspace Real.ℝPremetricSpace NegativeRealPredicate


negativeRealCoordinate : NegativeReal → Real.ℝ
negativeRealCoordinate = fst


negativeRealCoordinateIsContinuous :
  isContinuous
    (snd NegativeRealPremetricSpace)
    negativeRealCoordinate
    (snd Real.ℝPremetricSpace)
negativeRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        Real.ℝPremetricSpace NegativeRealPredicate))


negativeToPositiveNE :
  NE[ NegativeRealPremetricSpace , PositiveRealPremetricSpace ]
negativeToPositiveNE =
  restrictNE
    NegativeRealPredicate PositiveRealPredicate
    Neg.negationⁿ
    (λ _ x<0 → negativeNegationPositive x<0)


negativeToPositive : NegativeReal → PositiveReal
negativeToPositive = fst negativeToPositiveNE


negativeToPositiveIsContinuous :
  isContinuous
    (snd NegativeRealPremetricSpace)
    negativeToPositive
    (snd PositiveRealPremetricSpace)
negativeToPositiveIsContinuous =
  snd (NE→C negativeToPositiveNE)


private
  positiveReciprocalAfterNegativeInput :
    NegativeReal → Real.ℝ
  positiveReciprocalAfterNegativeInput =
    positiveRealReciprocal ∘ negativeToPositive

  positiveReciprocalAfterNegativeInputDerivative :
    NegativeReal → Real.ℝ
  positiveReciprocalAfterNegativeInputDerivative =
    positiveRealReciprocalDerivative ∘ negativeToPositive

  positiveReciprocalAfterNegativeInputHasDerivativeAlong :
    IsDerivativeAlong
      (snd NegativeRealPremetricSpace)
      (Neg.-_ ∘ negativeRealCoordinate)
      positiveReciprocalAfterNegativeInput
      positiveReciprocalAfterNegativeInputDerivative
  positiveReciprocalAfterNegativeInputHasDerivativeAlong =
    pullbackHasDerivativeAlong
      (snd NegativeRealPremetricSpace)
      (snd PositiveRealPremetricSpace)
      positiveRealCoordinate
      positiveRealReciprocal
      positiveRealReciprocalDerivative
      negativeToPositive
      negativeToPositiveIsContinuous
      positiveRealReciprocalHasDerivativeAlong


negativeRealReciprocal : NegativeReal → Real.ℝ
negativeRealReciprocal point =
  Neg.- positiveReciprocalAfterNegativeInput point


negativeRealReciprocalDerivative : NegativeReal → Real.ℝ
negativeRealReciprocalDerivative point =
  Neg.-
    (negativeRealReciprocal point Mul.·
      negativeRealReciprocal point)


negativeRealReciprocalHasDerivativeAlong :
  IsDerivativeAlong
    (snd NegativeRealPremetricSpace)
    negativeRealCoordinate
    negativeRealReciprocal
    negativeRealReciprocalDerivative
negativeRealReciprocalHasDerivativeAlong =
  subst2
    (IsDerivativeAlong
      (snd NegativeRealPremetricSpace)
      negativeRealCoordinate)
    function-path derivative-path raw-derivative
  where
  function-path :
    (Neg.-_ ∘ positiveReciprocalAfterNegativeInput)
      ≡ negativeRealReciprocal
  function-path = refl

  raw-derivative :
    IsDerivativeAlong
      (snd NegativeRealPremetricSpace)
      negativeRealCoordinate
      (Neg.-_ ∘ positiveReciprocalAfterNegativeInput)
      (Neg.-_ ∘
        (Neg.-_ ∘ positiveReciprocalAfterNegativeInputDerivative))
  raw-derivative =
    negHasDerivativeAlong
      (snd NegativeRealPremetricSpace)
      negativeRealCoordinate
      positiveReciprocalAfterNegativeInput
      (Neg.-_ ∘ positiveReciprocalAfterNegativeInputDerivative)
      (negCoordinateHasDerivativeAlong
        (snd NegativeRealPremetricSpace)
        negativeRealCoordinate
        positiveReciprocalAfterNegativeInput
        positiveReciprocalAfterNegativeInputDerivative
        positiveReciprocalAfterNegativeInputHasDerivativeAlong)

  derivative-path :
    (Neg.-_ ∘
      (Neg.-_ ∘ positiveReciprocalAfterNegativeInputDerivative))
      ≡
    negativeRealReciprocalDerivative
  derivative-path =
    funExt λ point →
      Neg.neg-involutive
        (positiveReciprocalAfterNegativeInputDerivative point)
      ∙ cong Neg.-_
          (sym
            (ℝRing.-Dist·
              (positiveReciprocalAfterNegativeInput point)
              (positiveReciprocalAfterNegativeInput point)))


negativeRealReciprocalIsContinuous :
  isContinuous
    (snd NegativeRealPremetricSpace)
    negativeRealReciprocal
    (snd Real.ℝPremetricSpace)
negativeRealReciprocalIsContinuous =
  snd
    (CategoryStructures._∘C_
      ( Neg.-_
      , isNonExpanding→isContinuous
          (snd Real.ℝPremetricSpace)
          Neg.-_
          (snd Real.ℝPremetricSpace)
          (snd Neg.negationⁿ)
      )
      ( positiveReciprocalAfterNegativeInput
      , snd
          (CategoryStructures._∘C_
            ( positiveRealReciprocal
            , positiveRealReciprocalIsContinuous
            )
            ( negativeToPositive
            , negativeToPositiveIsContinuous
            ))
      ))


negativeRealReciprocal≡inverseℝ :
  ∀ point →
  negativeRealReciprocal point
    ≡ inverseℝ (fst point) (inr (snd point))
negativeRealReciprocal≡inverseℝ point = refl


-- Quotients by the coordinate are now immediate consumers of the product
-- rule.  These forms retain the stronger subspace derivative and are useful
-- before passing to a pointwise nonvanishing denominator.

positiveRealDivideByCoordinate :
  (PositiveReal → Real.ℝ) → PositiveReal → Real.ℝ
positiveRealDivideByCoordinate numerator point =
  numerator point Mul.· positiveRealReciprocal point


positiveRealDivideByCoordinateDerivative :
  (numerator numerator-derivative : PositiveReal → Real.ℝ) →
  PositiveReal → Real.ℝ
positiveRealDivideByCoordinateDerivative
  numerator numerator-derivative point =
    (numerator-derivative point Mul.·
      positiveRealReciprocal point)
    Add.+
    (numerator point Mul.·
      positiveRealReciprocalDerivative point)


positiveRealDivideByCoordinateHasDerivativeAlong :
  (numerator numerator-derivative : PositiveReal → Real.ℝ) →
  IsDerivativeAlong
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    numerator numerator-derivative →
  IsDerivativeAlong
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    (positiveRealDivideByCoordinate numerator)
    (positiveRealDivideByCoordinateDerivative
      numerator numerator-derivative)
positiveRealDivideByCoordinateHasDerivativeAlong
  numerator numerator-derivative numerator-has-derivative =
  mulHasDerivativeAlong
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    numerator positiveRealReciprocal
    numerator-derivative positiveRealReciprocalDerivative
    positiveRealCoordinateIsContinuous
    numerator-has-derivative
    positiveRealReciprocalHasDerivativeAlong
