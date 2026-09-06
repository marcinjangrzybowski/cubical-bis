module Cubical.Analysis.Real.Calculus.Derivative.SignedReciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)

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
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (negSub)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Algebra.Inverse.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Reciprocal


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  reciprocalDifferenceFactorizationFromLaw :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate reciprocal : A → ℝ) →
    (∀ point → coordinate point · reciprocal point ≡ 1ℝ) →
    ∀ x y →
    reciprocal y - reciprocal x
      ≡
    (coordinate y - coordinate x) ·
      (- (reciprocal x · reciprocal y))
  reciprocalDifferenceFactorizationFromLaw
    coordinate reciprocal reciprocal-law x y =
      cong₂ _-_
        reciprocal-y-as-x-product
        reciprocal-x-as-y-product
    ∙ sym
        (ℝRing.·DistL-
          (coordinate x) (coordinate y) reciprocal-product)
    ∙ cong
        (_· reciprocal-product)
        (sym (negSub (coordinate y) (coordinate x)))
    ∙ ℝRing.-DistL·
        (coordinate y - coordinate x) reciprocal-product
    ∙ sym
        (ℝRing.-DistR·
          (coordinate y - coordinate x) reciprocal-product)
    where
    reciprocal-x : ℝ
    reciprocal-x = reciprocal x

    reciprocal-y : ℝ
    reciprocal-y = reciprocal y

    reciprocal-product : ℝ
    reciprocal-product = reciprocal-x · reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y ≡ coordinate x · reciprocal-product
    reciprocal-y-as-x-product =
      sym (mulIdL reciprocal-y)
      ∙ cong
          (_· reciprocal-y)
          (sym (reciprocal-law x))
      ∙ sym
          (mulAssoc
            (coordinate x) reciprocal-x reciprocal-y)

    reciprocal-x-as-y-product :
      reciprocal-x ≡ coordinate y · reciprocal-product
    reciprocal-x-as-y-product =
      sym (mulIdR reciprocal-x)
      ∙ cong
          (reciprocal-x ·_)
          (sym (reciprocal-law y))
      ∙ mulAssoc reciprocal-x (coordinate y) reciprocal-y
      ∙ cong
          (_· reciprocal-y)
          (mulComm reciprocal-x (coordinate y))
      ∙ sym
          (mulAssoc
            (coordinate y) reciprocal-x reciprocal-y)


-- A quantitative negative domain is the reflection of the positive domain.

UpperBoundedNegativePredicate : ℚ₊ → ℙ ℝ
UpperBoundedNegativePredicate η x =
  (x ≤ℝ - rat (fst η)) , isProp≤ℝ x (- rat (fst η))


UpperBoundedNegative : ℚ₊ → Type
UpperBoundedNegative η =
  Σ[ x ∈ ℝ ] x ∈ UpperBoundedNegativePredicate η


UpperBoundedNegativePremetricSpace :
  ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
UpperBoundedNegativePremetricSpace η =
  PremetricSubspace
    ℝPremetricSpace (UpperBoundedNegativePredicate η)


upperBoundedNegativeCoordinate :
  ∀ η → UpperBoundedNegative η → ℝ
upperBoundedNegativeCoordinate η = fst


upperBoundedNegativeMagnitude :
  ∀ η → UpperBoundedNegative η → LowerBoundedPositive η
upperBoundedNegativeMagnitude η point =
  - fst point
  , subst
      (_≤ℝ (- fst point))
      (negInvol (rat (fst η)))
      (negPres≤
        (fst point) (- rat (fst η)) (snd point))


upperBoundedNegativeMagnitudeIsContinuous :
  ∀ η →
  isContinuous
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeMagnitude η)
    (LowerBoundedPositivePremetricSpace η .snd)
upperBoundedNegativeMagnitudeIsContinuous η =
  isNonExpanding→isContinuous
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeMagnitude η)
    (LowerBoundedPositivePremetricSpace η .snd)
    λ where
      .IsNonExpanding.pres≈ x y ε close →
        neg-isNonExpanding .IsNonExpanding.pres≈
          (fst x) (fst y) ε close


upperBoundedNegativeReciprocal :
  ∀ η → UpperBoundedNegative η → ℝ
upperBoundedNegativeReciprocal η point =
  - lowerBoundedPositiveReciprocal η
      (upperBoundedNegativeMagnitude η point)


upperBoundedNegativeReciprocalDerivative :
  ∀ η → UpperBoundedNegative η → ℝ
upperBoundedNegativeReciprocalDerivative η point =
  - (upperBoundedNegativeReciprocal η point ·
      upperBoundedNegativeReciprocal η point)


upperBoundedNegativeReciprocalIsContinuous :
  ∀ η →
  isContinuous
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeReciprocal η)
    (ℝPremetricSpace .snd)
upperBoundedNegativeReciprocalIsContinuous η =
  snd
    (CategoryStructures._∘C_
      ( -_ , neg-isContinuous )
      ( lowerBoundedPositiveReciprocal η ∘
          upperBoundedNegativeMagnitude η
      , snd
          (CategoryStructures._∘C_
            ( lowerBoundedPositiveReciprocal η
            , lowerBoundedPositiveReciprocalIsContinuous η
            )
            ( upperBoundedNegativeMagnitude η
            , upperBoundedNegativeMagnitudeIsContinuous η
            ))
      ))


upperBoundedNegativeReciprocalLaw :
  ∀ η (point : UpperBoundedNegative η) →
  fst point · upperBoundedNegativeReciprocal η point ≡ 1ℝ
upperBoundedNegativeReciprocalLaw η point =
  sym
    (ℝRing.-Swap·
      (fst point)
      (lowerBoundedPositiveReciprocal η magnitude))
  ∙ boundedReciprocalLaw η (- fst point) (snd magnitude)
  where
  magnitude : LowerBoundedPositive η
  magnitude = upperBoundedNegativeMagnitude η point


upperBoundedNegativeReciprocalDifferenceFactor :
  ∀ η →
  UpperBoundedNegative η × UpperBoundedNegative η → ℝ
upperBoundedNegativeReciprocalDifferenceFactor η (x , y) =
  - (upperBoundedNegativeReciprocal η x ·
      upperBoundedNegativeReciprocal η y)


private
  upperBoundedNegativeReciprocalDifferenceFactorization :
    ∀ η (x y : UpperBoundedNegative η) →
    upperBoundedNegativeReciprocal η y -
        upperBoundedNegativeReciprocal η x
      ≡
    (fst y - fst x) ·
      upperBoundedNegativeReciprocalDifferenceFactor η (x , y)
  upperBoundedNegativeReciprocalDifferenceFactorization η =
    reciprocalDifferenceFactorizationFromLaw
      (upperBoundedNegativeCoordinate η)
      (upperBoundedNegativeReciprocal η)
      (upperBoundedNegativeReciprocalLaw η)

  upperBoundedNegativeReciprocalDifferenceFactorDiagonal :
    ∀ η (x : UpperBoundedNegative η) →
    upperBoundedNegativeReciprocalDifferenceFactor η (x , x)
      ≡
    upperBoundedNegativeReciprocalDerivative η x
  upperBoundedNegativeReciprocalDifferenceFactorDiagonal η x =
    refl

  upperBoundedNegativeReciprocalDifferenceFactorIsContinuous :
    ∀ η →
    isContinuous
      (PremetricProductStr
        (UpperBoundedNegativePremetricSpace η .snd)
        (UpperBoundedNegativePremetricSpace η .snd))
      (upperBoundedNegativeReciprocalDifferenceFactor η)
      (ℝPremetricSpace .snd)
  upperBoundedNegativeReciprocalDifferenceFactorIsContinuous η =
    snd
      (CategoryStructures._∘C_
        ( -_ , neg-isContinuous )
        ( (λ points →
              upperBoundedNegativeReciprocal η (fst points) ·
                upperBoundedNegativeReciprocal η (snd points))
        , mulOfContinuousIsContinuous
            (PremetricProductStr
              (UpperBoundedNegativePremetricSpace η .snd)
              (UpperBoundedNegativePremetricSpace η .snd))
            (upperBoundedNegativeReciprocal η ∘ fst)
            (upperBoundedNegativeReciprocal η ∘ snd)
            (snd
              (CategoryStructures._∘C_
                ( upperBoundedNegativeReciprocal η
                , upperBoundedNegativeReciprocalIsContinuous η
                )
                (productFstC
                  {M = UpperBoundedNegativePremetricSpace η}
                  {N = UpperBoundedNegativePremetricSpace η})))
            (snd
              (CategoryStructures._∘C_
                ( upperBoundedNegativeReciprocal η
                , upperBoundedNegativeReciprocalIsContinuous η
                )
                (productSndC
                  {M = UpperBoundedNegativePremetricSpace η}
                  {N = UpperBoundedNegativePremetricSpace η})))
        ))


upperBoundedNegativeReciprocalHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeCoordinate η)
    (upperBoundedNegativeReciprocal η)
    (upperBoundedNegativeReciprocalDerivative η)
upperBoundedNegativeReciprocalHasDerivativeAlong η =
  continuousDifferenceFactorGivesDerivative
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeCoordinate η)
    (upperBoundedNegativeReciprocal η)
    (upperBoundedNegativeReciprocalDerivative η)
    (upperBoundedNegativeReciprocalDifferenceFactor η)
    (upperBoundedNegativeReciprocalDifferenceFactorization η)
    (upperBoundedNegativeReciprocalDifferenceFactorDiagonal η)
    (upperBoundedNegativeReciprocalDifferenceFactorIsContinuous η)


upperBoundedNegativeIsNegative :
  ∀ η (point : UpperBoundedNegative η) →
  fst point <ℝ 0ℝ
upperBoundedNegativeIsNegative η point =
  positiveNegationNegative {x = fst point}
    (lowerBoundedPositiveIsPositive η
      (upperBoundedNegativeMagnitude η point))


inverseReciprocalOnUpperBound :
  ∀ η → UpperBoundedNegative η → ℝ
inverseReciprocalOnUpperBound η point =
  inverseℝ (fst point)
    (inr (upperBoundedNegativeIsNegative η point))


inverseReciprocalOnUpperBoundDerivative :
  ∀ η → UpperBoundedNegative η → ℝ
inverseReciprocalOnUpperBoundDerivative η point =
  - (inverseReciprocalOnUpperBound η point ·
      inverseReciprocalOnUpperBound η point)


inverseReciprocalOnUpperBound≡bounded :
  ∀ η (point : UpperBoundedNegative η) →
  inverseReciprocalOnUpperBound η point
    ≡ upperBoundedNegativeReciprocal η point
inverseReciprocalOnUpperBound≡bounded η point =
  cong (-_)
    (cong
        (positiveReciprocal (- fst point))
        (isProp<ℝ 0ℝ (- fst point)
          (negativeNegationPositive
            {x = fst point}
            (upperBoundedNegativeIsNegative η point))
          (lowerBoundedPositiveIsPositive η magnitude))
    ∙ positiveReciprocalOnLowerBound≡bounded η magnitude)
  where
  magnitude : LowerBoundedPositive η
  magnitude = upperBoundedNegativeMagnitude η point


inverseReciprocalOnUpperBoundHasDerivativeAlong :
  ∀ η →
  IsDerivativeAlong
    (UpperBoundedNegativePremetricSpace η .snd)
    (upperBoundedNegativeCoordinate η)
    (inverseReciprocalOnUpperBound η)
    (inverseReciprocalOnUpperBoundDerivative η)
inverseReciprocalOnUpperBoundHasDerivativeAlong η =
  subst2
    (IsDerivativeAlong
      (UpperBoundedNegativePremetricSpace η .snd)
      (upperBoundedNegativeCoordinate η))
    (sym function-path)
    (sym derivative-path)
    (upperBoundedNegativeReciprocalHasDerivativeAlong η)
  where
  function-path :
    inverseReciprocalOnUpperBound η
      ≡ upperBoundedNegativeReciprocal η
  function-path =
    funExt (inverseReciprocalOnUpperBound≡bounded η)

  derivative-path :
    inverseReciprocalOnUpperBoundDerivative η
      ≡ upperBoundedNegativeReciprocalDerivative η
  derivative-path =
    funExt λ point →
      cong (-_)
        (cong₂ _·_
          (inverseReciprocalOnUpperBound≡bounded η point)
          (inverseReciprocalOnUpperBound≡bounded η point))
