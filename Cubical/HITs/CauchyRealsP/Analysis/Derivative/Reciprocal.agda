module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Reciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

-- A fixed positive rational lower bound is enough to make the bounded
-- reciprocal agree with the genuine reciprocal law.  Keeping that bound in
-- the domain is more informative constructively than hiding it behind a
-- nonzero hypothesis.
LowerBoundedPositivePredicate :
  ℚ₊ → ℙ ℝ
LowerBoundedPositivePredicate η x =
  (rat (fst η) ≤ℝ x)
  , isProp≤ℝ (rat (fst η)) x

LowerBoundedPositive :
  ℚ₊ → Type
LowerBoundedPositive η =
  Σ[ x ∈ ℝ ]
    x ∈ LowerBoundedPositivePredicate η

LowerBoundedPositivePremetricSpace :
  ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
LowerBoundedPositivePremetricSpace η =
  PremetricSubspace
    ℝPremetricSpace
    (LowerBoundedPositivePredicate η)

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
  - (lowerBoundedPositiveReciprocal η point
      · lowerBoundedPositiveReciprocal η point)

lowerBoundedPositiveCoordinateIsContinuous :
  ∀ η →
  isContinuous
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (snd ℝPremetricSpace)
lowerBoundedPositiveCoordinateIsContinuous η =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace
        (LowerBoundedPositivePredicate η)))

boundedReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (snd ℝPremetricSpace)
    (boundedReciprocalℝ η)
    (snd ℝPremetricSpace)
boundedReciprocalIsContinuous η =
  isLipschitz→isContinuous
    (snd ℝPremetricSpace)
    (boundedReciprocalℝ η)
    (snd ℝPremetricSpace)
    ∣ reciprocalLipschitzBound η
      , boundedReciprocalIsLipschitz η ∣₁

lowerBoundedPositiveReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveReciprocal η)
    (snd ℝPremetricSpace)
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
    × LowerBoundedPositive η → ℝ
lowerBoundedPositiveReciprocalDifferenceFactor
  η (x , y) =
    - (lowerBoundedPositiveReciprocal η x
        · lowerBoundedPositiveReciprocal η y)

private
  reciprocalDifferenceFactorization :
    ∀ η (x y : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocal η y
        - lowerBoundedPositiveReciprocal η x
      ≡
    (fst y - fst x)
      · lowerBoundedPositiveReciprocalDifferenceFactor
          η (x , y)
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
    reciprocal-x =
      lowerBoundedPositiveReciprocal η x

    reciprocal-y : ℝ
    reciprocal-y =
      lowerBoundedPositiveReciprocal η y

    reciprocal-product : ℝ
    reciprocal-product =
      reciprocal-x · reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y
        ≡
      fst x · reciprocal-product
    reciprocal-y-as-x-product =
      sym (mulIdL reciprocal-y)
      ∙ cong
          (_· reciprocal-y)
          (sym
            (boundedReciprocalLaw
              η (fst x) (snd x)))
      ∙ mulAssoc
          (fst x) reciprocal-x reciprocal-y

    reciprocal-x-as-y-product :
      reciprocal-x
        ≡
      fst y · reciprocal-product
    reciprocal-x-as-y-product =
      sym (mulIdR reciprocal-x)
      ∙ cong
          (reciprocal-x ·_)
          (sym
            (boundedReciprocalLaw
              η (fst y) (snd y)))
      ∙ sym
          (mulAssoc
            reciprocal-x (fst y) reciprocal-y)
      ∙ cong
          (_· reciprocal-y)
          (mulComm reciprocal-x (fst y))
      ∙ mulAssoc
          (fst y) reciprocal-x reciprocal-y

  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal :
    ∀ η (x : LowerBoundedPositive η) →
    lowerBoundedPositiveReciprocalDifferenceFactor
        η (x , x)
      ≡
    lowerBoundedPositiveReciprocalDerivative η x
  lowerBoundedPositiveReciprocalDifferenceFactorDiagonal
    η x =
      refl

  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous :
    ∀ η →
    isContinuous
      (PremetricProductStr
        (snd (LowerBoundedPositivePremetricSpace η))
        (snd (LowerBoundedPositivePremetricSpace η)))
      (lowerBoundedPositiveReciprocalDifferenceFactor η)
      (snd ℝPremetricSpace)
  lowerBoundedPositiveReciprocalDifferenceFactorIsContinuous η =
    snd
      (CategoryStructures._∘C_
        ( (-_)
        , isNonExpanding→isContinuous
            (snd ℝPremetricSpace)
            (-_)
            (snd ℝPremetricSpace)
            negIsNonExpanding
        )
        ( (λ points →
              lowerBoundedPositiveReciprocal η (fst points)
                · lowerBoundedPositiveReciprocal η (snd points))
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

-- The fixed bound itself supplies a canonical positive-gap representative.
-- This identifies the checked bounded function with the proof-independent
-- positive reciprocal already used by the algebra layer.
lowerBoundedPositiveGap :
  ∀ η (point : LowerBoundedPositive η) →
  PositiveGap 0 (fst point)
lowerBoundedPositiveGap η point =
  positiveGap η
    (gapBoundIntro
      0 (fst point) η
      (subst
        (_≤ℝ fst point)
        (sym (addIdL (rat (fst η))))
        (snd point)))

lowerBoundedPositiveIsPositive :
  ∀ η (point : LowerBoundedPositive η) →
  0 <ℝ fst point
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
  - (positiveReciprocalOnLowerBound η point
      · positiveReciprocalOnLowerBound η point)

positiveReciprocalOnLowerBound≡bounded :
  ∀ η (point : LowerBoundedPositive η) →
  positiveReciprocalOnLowerBound η point
    ≡ lowerBoundedPositiveReciprocal η point
positiveReciprocalOnLowerBound≡bounded η point =
  cong
      (positiveReciprocal (fst point))
      (isProp<ℝ 0 (fst point)
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
    funExt
      (positiveReciprocalOnLowerBound≡bounded η)

  derivative-path :
    positiveReciprocalOnLowerBoundDerivative η
      ≡ lowerBoundedPositiveReciprocalDerivative η
  derivative-path =
    funExt
      (λ point →
        cong (-_)
          (cong₂ _·_
            (positiveReciprocalOnLowerBound≡bounded η point)
            (positiveReciprocalOnLowerBound≡bounded η point)))

-- The full positive subspace needs no globally selected lower bound.  At a
-- point, a positive-gap representative is halved; a neighbourhood of that
-- radius remains above the half-gap, so the fixed-bound theorem applies
-- locally.  The target derivative modulus is proposition-valued, allowing
-- the original truncated gap to be eliminated coherently.
PositiveRealPredicate : ℙ ℝ
PositiveRealPredicate x =
  (0 <ℝ x) , isProp<ℝ 0 x

PositiveReal : Type
PositiveReal =
  Σ[ x ∈ ℝ ] x ∈ PositiveRealPredicate

PositiveRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
PositiveRealPremetricSpace =
  PremetricSubspace
    ℝPremetricSpace PositiveRealPredicate

positiveRealCoordinate : PositiveReal → ℝ
positiveRealCoordinate = fst

positiveRealCoordinateIsContinuous :
  isContinuous
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    (snd ℝPremetricSpace)
positiveRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace PositiveRealPredicate))

positiveRealReciprocal : PositiveReal → ℝ
positiveRealReciprocal point =
  positiveReciprocal (fst point) (snd point)

positiveRealReciprocalDerivative : PositiveReal → ℝ
positiveRealReciprocalDerivative point =
  - (positiveRealReciprocal point
      · positiveRealReciprocal point)

private
  halfGapLowerBound :
    ∀ {x} (w : PositiveGap 0 x) →
    rat (fst (width w /2₊)) ≤ℝ x
  halfGapLowerBound {x} w =
    ≤ℝ-trans
      (rat (fst (width w /2₊)))
      (rat (fst (width w))) x
      (≤ℚ→≤ℝ
        (fst (width w /2₊))
        (fst (width w))
        (ℚ.<Weaken≤ _ _ (/2₊<id (width w))))
      (gapLowerBound w)

  halfGapBelowShiftedPoint :
    ∀ {x} (w : PositiveGap 0 x) →
    rat (fst (width w /2₊))
      ≤ℝ x - rat (fst (width w /2₊))
  halfGapBelowShiftedPoint {x} w =
    subst2 _≤ℝ_
      cancel-right-half
      refl
      (≤ℝ-addR
        (half + half) x (- half)
        two-halves-below-x)
    where
    half : ℝ
    half = rat (fst (width w /2₊))

    two-halves-path :
      half + half ≡ rat (fst (width w))
    two-halves-path =
      rat+rat
        (fst (width w /2₊))
        (fst (width w /2₊))
      ∙ cong rat
          (1/2∈ℚ./2+/2≡id
            (fst (width w)))

    two-halves-below-x :
      half + half ≤ℝ x
    two-halves-below-x =
      subst
        (_≤ℝ x)
        (sym two-halves-path)
        (gapLowerBound w)

    cancel-right-half :
      (half + half) + (- half) ≡ half
    cancel-right-half =
      addSubCancel half half

  nearRealPointAboveHalfGap :
    ∀ (x y : ℝ)
      (w : PositiveGap 0 x) →
    x ∼[ width w /2₊ ] y →
    rat (fst (width w /2₊)) ≤ℝ y
  nearRealPointAboveHalfGap x y w x∼y =
    ≤ℝ-trans
      (rat (fst (width w /2₊)))
      (x - rat (fst (width w /2₊)))
      y
      (halfGapBelowShiftedPoint w)
      (close→lowerBound
        y x (width w /2₊)
        (sym∼
          x y (width w /2₊) x∼y))

positiveGapHalfNeighbourPositive :
  ∀ (x y : ℝ) (w : PositiveGap 0 x) →
  x ∼[ width w /2₊ ] y →
  0 <ℝ y
positiveGapHalfNeighbourPositive x y w x∼y =
  lowerBoundedPositiveIsPositive
    (width w /2₊)
    ( y
    , nearRealPointAboveHalfGap x y w x∼y
    )

positiveRealReciprocalHasDerivativeAlong :
  IsDerivativeAlong
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    positiveRealReciprocal
    positiveRealReciprocalDerivative
positiveRealReciprocalHasDerivativeAlong x ε =
  PT.rec squash₁ derivative-at-gap (snd x)
  where
  derivative-at-gap :
    PositiveGap 0 (fst x) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_
          (snd PositiveRealPremetricSpace) x δ y →
        absℝ
            (derivativeErrorAlong
              positiveRealCoordinate
              positiveRealReciprocal
              positiveRealReciprocalDerivative
              x y)
          ≤ℝ
        rat (fst ε)
          · absℝ (fst y - fst x))
  derivative-at-gap w =
    PT.map convert-local-bound
      (positiveReciprocalOnLowerBoundHasDerivativeAlong
        half-width x-at-half ε)
    where
    half-width : ℚ₊
    half-width = width w /2₊

    x-at-half : LowerBoundedPositive half-width
    x-at-half =
      fst x , halfGapLowerBound w

    convert-local-bound :
      Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd (LowerBoundedPositivePremetricSpace half-width))
            x-at-half δ y →
          absℝ
              (derivativeErrorAlong
                (lowerBoundedPositiveCoordinate half-width)
                (positiveReciprocalOnLowerBound half-width)
                (positiveReciprocalOnLowerBoundDerivative half-width)
                x-at-half y)
            ≤ℝ
          rat (fst ε)
            · absℝ (fst y - fst x))
      →
      Σ[ κ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd PositiveRealPremetricSpace) x κ y →
          absℝ
              (derivativeErrorAlong
                positiveRealCoordinate
                positiveRealReciprocal
                positiveRealReciprocalDerivative
                x y)
            ≤ℝ
          rat (fst ε)
            · absℝ (fst y - fst x))
    convert-local-bound (δ , fixed-bound) =
      min₊ δ half-width
      , λ y x∼y →
          let
            x∼δy :
              PremetricStr._≈[_]_
                (snd PositiveRealPremetricSpace) x δ y
            x∼δy =
              PremetricStr.isMonotone≈≤
                (snd PositiveRealPremetricSpace)
                x y (min₊ δ half-width) δ
                (min₊≤L δ half-width) x∼y

            x∼halfy : fst x ∼[ half-width ] fst y
            x∼halfy =
              PremetricStr.isMonotone≈≤
                (snd PositiveRealPremetricSpace)
                x y (min₊ δ half-width) half-width
                (min₊≤R δ half-width) x∼y

            y-at-half : LowerBoundedPositive half-width
            y-at-half =
              fst y
              , nearRealPointAboveHalfGap
                  (fst x) (fst y) w x∼halfy

            fixed-error-bound =
              fixed-bound y-at-half x∼δy

            function-x-path :
              positiveReciprocalOnLowerBound
                  half-width x-at-half
                ≡
              positiveRealReciprocal x
            function-x-path =
              cong
                (positiveReciprocal (fst x))
                (isProp<ℝ 0 (fst x)
                  (lowerBoundedPositiveIsPositive
                    half-width x-at-half)
                  (snd x))

            function-y-path :
              positiveReciprocalOnLowerBound
                  half-width y-at-half
                ≡
              positiveRealReciprocal y
            function-y-path =
              cong
                (positiveReciprocal (fst y))
                (isProp<ℝ 0 (fst y)
                  (lowerBoundedPositiveIsPositive
                    half-width y-at-half)
                  (snd y))

            derivative-x-path :
              positiveReciprocalOnLowerBoundDerivative
                  half-width x-at-half
                ≡
              positiveRealReciprocalDerivative x
            derivative-x-path =
              cong (-_)
                (cong₂ _·_
                  function-x-path function-x-path)

            error-path :
              derivativeErrorAlong
                  positiveRealCoordinate
                  positiveRealReciprocal
                  positiveRealReciprocalDerivative
                  x y
                ≡
              derivativeErrorAlong
                  (lowerBoundedPositiveCoordinate half-width)
                  (positiveReciprocalOnLowerBound half-width)
                  (positiveReciprocalOnLowerBoundDerivative half-width)
                  x-at-half y-at-half
            error-path =
              cong₂ _-_
                (cong₂ _-_
                  (sym function-y-path)
                  (sym function-x-path))
                (cong
                  (_· (fst y - fst x))
                  (sym derivative-x-path))
          in
          subst
            (λ error →
              absℝ error
                ≤ℝ
              rat (fst ε)
                · absℝ (fst y - fst x))
            (sym error-path)
            fixed-error-bound

positiveRealReciprocalIsContinuous :
  isContinuous
    (snd PositiveRealPremetricSpace)
    positiveRealReciprocal
    (snd ℝPremetricSpace)
positiveRealReciprocalIsContinuous =
  derivativeAlongIsContinuous
    (snd PositiveRealPremetricSpace)
    positiveRealCoordinate
    positiveRealReciprocal
    positiveRealReciprocalDerivative
    positiveRealCoordinateIsContinuous
    positiveRealReciprocalHasDerivativeAlong

NegativeRealPredicate : ℙ ℝ
NegativeRealPredicate x =
  (x <ℝ 0) , isProp<ℝ x 0

NegativeReal : Type
NegativeReal =
  Σ[ x ∈ ℝ ] x ∈ NegativeRealPredicate

NegativeRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
NegativeRealPremetricSpace =
  PremetricSubspace
    ℝPremetricSpace NegativeRealPredicate

negativeRealCoordinate : NegativeReal → ℝ
negativeRealCoordinate = fst

negativeRealCoordinateIsContinuous :
  isContinuous
    (snd NegativeRealPremetricSpace)
    negativeRealCoordinate
    (snd ℝPremetricSpace)
negativeRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace NegativeRealPredicate))

negativeToPositiveNE :
  NE[ NegativeRealPremetricSpace , PositiveRealPremetricSpace ]
negativeToPositiveNE =
  restrictNE
    NegativeRealPredicate PositiveRealPredicate
    ((-_ ) , negIsNonExpanding)
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
    NegativeReal → ℝ
  positiveReciprocalAfterNegativeInput =
    positiveRealReciprocal ∘ negativeToPositive

  positiveReciprocalAfterNegativeInputDerivative :
    NegativeReal → ℝ
  positiveReciprocalAfterNegativeInputDerivative =
    positiveRealReciprocalDerivative ∘ negativeToPositive

  positiveReciprocalAfterNegativeInputHasDerivativeAlong :
    IsDerivativeAlong
      (snd NegativeRealPremetricSpace)
      (λ point → - negativeRealCoordinate point)
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

negativeRealReciprocal : NegativeReal → ℝ
negativeRealReciprocal point =
  - positiveReciprocalAfterNegativeInput point

negativeRealReciprocalDerivative : NegativeReal → ℝ
negativeRealReciprocalDerivative point =
  - (negativeRealReciprocal point
      · negativeRealReciprocal point)

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
    function-path derivative-path
    raw-derivative
  where
  raw-derivative :
    IsDerivativeAlong
      (snd NegativeRealPremetricSpace)
      negativeRealCoordinate
      (λ point →
        - positiveReciprocalAfterNegativeInput point)
      (λ point →
        - (- positiveReciprocalAfterNegativeInputDerivative point))
  raw-derivative =
    negHasDerivativeAlong
      (snd NegativeRealPremetricSpace)
      negativeRealCoordinate
      positiveReciprocalAfterNegativeInput
      (λ point →
        - positiveReciprocalAfterNegativeInputDerivative point)
      (negCoordinateHasDerivativeAlong
        (snd NegativeRealPremetricSpace)
        negativeRealCoordinate
        positiveReciprocalAfterNegativeInput
        positiveReciprocalAfterNegativeInputDerivative
        positiveReciprocalAfterNegativeInputHasDerivativeAlong)

  function-path :
    (λ point →
      - positiveReciprocalAfterNegativeInput point)
      ≡
    negativeRealReciprocal
  function-path =
    refl

  derivative-path :
    (λ point →
      - (- positiveReciprocalAfterNegativeInputDerivative point))
      ≡
    negativeRealReciprocalDerivative
  derivative-path =
    funExt λ point →
      negInvol
        (positiveReciprocalAfterNegativeInputDerivative point)
      ∙ cong (-_)
          (sym
            (ℝRing.-Dist·
              (positiveReciprocalAfterNegativeInput point)
              (positiveReciprocalAfterNegativeInput point)))

negativeRealReciprocalIsContinuous :
  isContinuous
    (snd NegativeRealPremetricSpace)
    negativeRealReciprocal
    (snd ℝPremetricSpace)
negativeRealReciprocalIsContinuous =
  derivativeAlongIsContinuous
    (snd NegativeRealPremetricSpace)
    negativeRealCoordinate
    negativeRealReciprocal
    negativeRealReciprocalDerivative
    negativeRealCoordinateIsContinuous
    negativeRealReciprocalHasDerivativeAlong

negativeRealReciprocal≡inverseℝ :
  ∀ point →
  negativeRealReciprocal point
    ≡ inverseℝ (fst point) (inr (snd point))
negativeRealReciprocal≡inverseℝ point =
  refl

-- Division by the positive coordinate is now a derivative-algebra consumer,
-- rather than a second divided-difference proof.  This formulation accepts
-- any numerator already differentiated relative to the same subspace.
lowerBoundedPositiveDivideByCoordinate :
  ∀ η →
  (LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
lowerBoundedPositiveDivideByCoordinate
  η numerator point =
    numerator point
      · positiveReciprocalOnLowerBound η point

lowerBoundedPositiveDivideByCoordinateDerivative :
  ∀ η →
  (numerator numerator-derivative :
    LowerBoundedPositive η → ℝ) →
  LowerBoundedPositive η → ℝ
lowerBoundedPositiveDivideByCoordinateDerivative
  η numerator numerator-derivative point =
    numerator-derivative point
        · positiveReciprocalOnLowerBound η point
      + numerator point
        · positiveReciprocalOnLowerBoundDerivative η point

lowerBoundedPositiveDivideByCoordinateHasDerivativeAlong :
  ∀ η
    (numerator numerator-derivative :
      LowerBoundedPositive η → ℝ) →
  IsDerivativeAlong
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    numerator numerator-derivative →
  IsDerivativeAlong
    (snd (LowerBoundedPositivePremetricSpace η))
    (lowerBoundedPositiveCoordinate η)
    (lowerBoundedPositiveDivideByCoordinate η numerator)
    (lowerBoundedPositiveDivideByCoordinateDerivative
      η numerator numerator-derivative)
lowerBoundedPositiveDivideByCoordinateHasDerivativeAlong
  η numerator numerator-derivative
  numerator-has-derivative =
    mulHasDerivativeAlong
      (snd (LowerBoundedPositivePremetricSpace η))
      (lowerBoundedPositiveCoordinate η)
      numerator
      (positiveReciprocalOnLowerBound η)
      numerator-derivative
      (positiveReciprocalOnLowerBoundDerivative η)
      (lowerBoundedPositiveCoordinateIsContinuous η)
      numerator-has-derivative
      (positiveReciprocalOnLowerBoundHasDerivativeAlong η)

positiveRealDivideByCoordinate :
  (PositiveReal → ℝ) → PositiveReal → ℝ
positiveRealDivideByCoordinate numerator point =
  numerator point · positiveRealReciprocal point

positiveRealDivideByCoordinateDerivative :
  (numerator numerator-derivative : PositiveReal → ℝ) →
  PositiveReal → ℝ
positiveRealDivideByCoordinateDerivative
  numerator numerator-derivative point =
    numerator-derivative point
        · positiveRealReciprocal point
      + numerator point
        · positiveRealReciprocalDerivative point

positiveRealDivideByCoordinateHasDerivativeAlong :
  (numerator numerator-derivative : PositiveReal → ℝ) →
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
  numerator numerator-derivative
  numerator-has-derivative =
    mulHasDerivativeAlong
      (snd PositiveRealPremetricSpace)
      positiveRealCoordinate
      numerator positiveRealReciprocal
      numerator-derivative positiveRealReciprocalDerivative
      positiveRealCoordinateIsContinuous
      numerator-has-derivative
      positiveRealReciprocalHasDerivativeAlong
