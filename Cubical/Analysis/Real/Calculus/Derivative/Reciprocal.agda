module Cubical.Analysis.Real.Calculus.Derivative.Reciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-weaken)
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded
open import Cubical.Analysis.Real.Algebra.Inverse.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.OpenSubspace


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Retaining a positive rational lower bound in the domain makes reciprocal
-- globally Lipschitz there and supplies the untruncated inverse law needed
-- by the difference-factor proof.

LowerBoundedPositivePredicate : ℚ₊ → ℙ ℝ
LowerBoundedPositivePredicate η x =
  (rat (fst η) ≤ℝ x) , isProp≤ℝ (rat (fst η)) x


LowerBoundedPositive : ℚ₊ → Type
LowerBoundedPositive η =
  Σ[ x ∈ ℝ ] x ∈ LowerBoundedPositivePredicate η


LowerBoundedPositivePremetricSpace :
  ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
LowerBoundedPositivePremetricSpace η =
  PremetricSubspace
    ℝPremetricSpace (LowerBoundedPositivePredicate η)


lowerBoundedPositiveCoordinate :
  ∀ η → LowerBoundedPositive η → ℝ
lowerBoundedPositiveCoordinate η = fst


lowerBoundedPositiveReciprocal :
  ∀ η → LowerBoundedPositive η → ℝ
lowerBoundedPositiveReciprocal η point =
  boundedReciprocalℝ η (fst point)


lowerBoundedPositiveReciprocalDerivative :
  ∀ η → LowerBoundedPositive η → ℝ
lowerBoundedPositiveReciprocalDerivative η point =
  - (lowerBoundedPositiveReciprocal η point ·
      lowerBoundedPositiveReciprocal η point)


lowerBoundedPositiveCoordinateIsContinuous :
  ∀ η →
  isContinuous
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (ℝPremetricSpace .snd)
lowerBoundedPositiveCoordinateIsContinuous η =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace
        (LowerBoundedPositivePredicate η)))


boundedReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (ℝPremetricSpace .snd)
    (boundedReciprocalℝ η)
    (ℝPremetricSpace .snd)
boundedReciprocalIsContinuous η =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd)
    (boundedReciprocalℝ η)
    (ℝPremetricSpace .snd)
    ∣ reciprocalLipschitzBound η
    , boundedReciprocalIsLipschitz η ∣₁


lowerBoundedPositiveReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveReciprocal η)
    (ℝPremetricSpace .snd)
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
  LowerBoundedPositive η × LowerBoundedPositive η → ℝ
lowerBoundedPositiveReciprocalDifferenceFactor η (x , y) =
  - (lowerBoundedPositiveReciprocal η x ·
      lowerBoundedPositiveReciprocal η y)


private
  negSub : ∀ x y → - (x - y) ≡ y - x
  negSub x y =
    negAdd x (- y)
    ∙ cong ((- x) +_) (negInvol y)
    ∙ addComm (- x) y

  reciprocalDifferenceFactorization :
    ∀ η (x y : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocal η y -
        lowerBoundedPositiveReciprocal η x
      ≡
    (fst y - fst x) ·
      lowerBoundedPositiveReciprocalDifferenceFactor η (x , y)
  reciprocalDifferenceFactorization η x y =
    cong₂ _-_
      reciprocal-y-as-x-product
      reciprocal-x-as-y-product
    ∙ sym
        (ℝRing.·DistL-
          (fst x) (fst y) reciprocal-product)
    ∙ cong
        (_· reciprocal-product)
        (sym (negSub (fst y) (fst x)))
    ∙ ℝRing.-DistL·
        (fst y - fst x) reciprocal-product
    ∙ sym
        (ℝRing.-DistR·
          (fst y - fst x) reciprocal-product)
    where
    reciprocal-x : ℝ
    reciprocal-x = lowerBoundedPositiveReciprocal η x

    reciprocal-y : ℝ
    reciprocal-y = lowerBoundedPositiveReciprocal η y

    reciprocal-product : ℝ
    reciprocal-product = reciprocal-x · reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y ≡ fst x · reciprocal-product
    reciprocal-y-as-x-product =
      sym (mulIdL reciprocal-y)
      ∙ cong
          (_· reciprocal-y)
          (sym (boundedReciprocalLaw η (fst x) (snd x)))
      ∙ sym (mulAssoc (fst x) reciprocal-x reciprocal-y)

    reciprocal-x-as-y-product :
      reciprocal-x ≡ fst y · reciprocal-product
    reciprocal-x-as-y-product =
      sym (mulIdR reciprocal-x)
      ∙ cong
          (reciprocal-x ·_)
          (sym (boundedReciprocalLaw η (fst y) (snd y)))
      ∙ mulAssoc reciprocal-x (fst y) reciprocal-y
      ∙ cong
          (_· reciprocal-y)
          (mulComm reciprocal-x (fst y))
      ∙ sym (mulAssoc (fst y) reciprocal-x reciprocal-y)

  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal :
    ∀ η (x : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocalDifferenceFactor η (x , x)
      ≡
    lowerBoundedPositiveReciprocalDerivative η x
  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal η x =
    refl

  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous :
    ∀ η →
    isContinuous
      (PremetricProductStr
        (LowerBoundedPositivePremetricSpace η .snd)
        (LowerBoundedPositivePremetricSpace η .snd))
      (lowerBoundedPositiveReciprocalDifferenceFactor η)
      (ℝPremetricSpace .snd)
  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous η =
    snd
      (CategoryStructures._∘C_
        ( -_
        , isNonExpanding→isContinuous
            (ℝPremetricSpace .snd)
            -_
            (ℝPremetricSpace .snd)
            neg-isNonExpanding
        )
        ( (λ points →
              lowerBoundedPositiveReciprocal η (fst points) ·
                lowerBoundedPositiveReciprocal η (snd points))
        , mulOfContinuousIsContinuous
            (PremetricProductStr
              (LowerBoundedPositivePremetricSpace η .snd)
              (LowerBoundedPositivePremetricSpace η .snd))
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
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveReciprocal η)
    (lowerBoundedPositiveReciprocalDerivative η)
lowerBoundedPositiveReciprocalHasDerivativeAlong η =
  continuousDifferenceFactorGivesDerivative
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveReciprocal η)
    (lowerBoundedPositiveReciprocalDerivative η)
    (lowerBoundedPositiveReciprocalDifferenceFactor η)
    (reciprocalDifferenceFactorization η)
    (lowerBoundedPositiveReciprocalDifferenceFactorDiagonal η)
    (lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous η)


lowerOpenHalfLineToLowerBoundedPositive :
  ∀ η →
  LowerOpenHalfLine (rat (fst η)) → LowerBoundedPositive η
lowerOpenHalfLineToLowerBoundedPositive η point =
  fst point
  , <ℝ-weaken
      (rat (fst η)) (fst point) (snd point)


lowerOpenHalfLineToLowerBoundedPositiveIsContinuous :
  ∀ η →
  isContinuous
    (LowerOpenHalfLinePremetricSpace (rat (fst η)) .snd)
    (lowerOpenHalfLineToLowerBoundedPositive η)
    (LowerBoundedPositivePremetricSpace η .snd)
lowerOpenHalfLineToLowerBoundedPositiveIsContinuous η =
  isNonExpanding→isContinuous
    (LowerOpenHalfLinePremetricSpace (rat (fst η)) .snd)
    (lowerOpenHalfLineToLowerBoundedPositive η)
    (LowerBoundedPositivePremetricSpace η .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ _ close → close


lowerOpenHalfLineReciprocalHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (LowerOpenHalfLinePremetricSpace (rat (fst η)) .snd)
    fst
    (boundedReciprocalℝ η ∘ fst)
    ((λ value →
        - (boundedReciprocalℝ η value ·
            boundedReciprocalℝ η value)) ∘ fst)
lowerOpenHalfLineReciprocalHasDerivativeAlong η =
  pullbackHasDerivativeAlong
    (LowerOpenHalfLinePremetricSpace (rat (fst η)) .snd)
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveReciprocal η)
    (lowerBoundedPositiveReciprocalDerivative η)
    (lowerOpenHalfLineToLowerBoundedPositive η)
    (lowerOpenHalfLineToLowerBoundedPositiveIsContinuous η)
    (lowerBoundedPositiveReciprocalHasDerivativeAlong η)


boundedReciprocalHasDerivativeAtAboveLowerBound :
  ∀ η x →
  rat (fst η) <ℝ x →
  IsDerivativeAt
    (boundedReciprocalℝ η)
    (- (boundedReciprocalℝ η x · boundedReciprocalℝ η x))
    x
boundedReciprocalHasDerivativeAtAboveLowerBound η x η<x =
  openSubspaceDerivativeAt
    (LowerOpenHalfLinePredicate (rat (fst η)))
    (lowerOpenHalfLineIsOpen (rat (fst η)))
    (boundedReciprocalℝ η)
    (λ value →
      - (boundedReciprocalℝ η value ·
          boundedReciprocalℝ η value))
    (lowerOpenHalfLineReciprocalHasDerivativeAlong η)
    x η<x


-- The bounded lift agrees with the proof-independent positive reciprocal
-- everywhere on the controlled domain, so the checked derivative transfers
-- without exposing the implementation of reciprocal.

lowerBoundedPositiveGap :
  ∀ η (point : LowerBoundedPositive η) →
  PositiveGap 0ℝ (fst point)
lowerBoundedPositiveGap η point =
  ( η
  , subst
      (_≤ℝ fst point)
      (sym (addIdL (rat (fst η))))
      (snd point)
  )


lowerBoundedPositiveIsPositive :
  ∀ η (point : LowerBoundedPositive η) →
  0ℝ <ℝ fst point
lowerBoundedPositiveIsPositive η point =
  ∣ lowerBoundedPositiveGap η point ∣₁


positiveReciprocalOnLowerBound :
  ∀ η → LowerBoundedPositive η → ℝ
positiveReciprocalOnLowerBound η point =
  positiveReciprocal
    (fst point)
    (lowerBoundedPositiveIsPositive η point)


positiveReciprocalOnLowerBoundDerivative :
  ∀ η → LowerBoundedPositive η → ℝ
positiveReciprocalOnLowerBoundDerivative η point =
  - (positiveReciprocalOnLowerBound η point ·
      positiveReciprocalOnLowerBound η point)


positiveReciprocalOnLowerBound≡bounded :
  ∀ η (point : LowerBoundedPositive η) →
  positiveReciprocalOnLowerBound η point
    ≡ lowerBoundedPositiveReciprocal η point
positiveReciprocalOnLowerBound≡bounded η point =
  cong
      (positiveReciprocal (fst point))
      (isProp<ℝ 0ℝ (fst point)
        (lowerBoundedPositiveIsPositive η point)
        ∣ lowerBoundedPositiveGap η point ∣₁)
  ∙ positiveReciprocalAtGap
      (fst point)
      (lowerBoundedPositiveGap η point)


positiveReciprocalOnLowerBoundHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (LowerBoundedPositivePremetricSpace η .snd)
    (lowerBoundedPositiveCoordinate η)
    (positiveReciprocalOnLowerBound η)
    (positiveReciprocalOnLowerBoundDerivative η)
positiveReciprocalOnLowerBoundHasDerivativeAlong η =
  subst2
    (IsDerivativeAlong
      (LowerBoundedPositivePremetricSpace η .snd)
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
      cong (-_)
        (cong₂ _·_
          (positiveReciprocalOnLowerBound≡bounded η point)
          (positiveReciprocalOnLowerBound≡bounded η point))
