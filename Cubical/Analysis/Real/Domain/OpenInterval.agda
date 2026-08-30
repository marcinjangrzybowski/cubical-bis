module Cubical.Analysis.Real.Domain.OpenInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open 1/2∈ℚ using (/2+/2≡id)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Metric
open import Cubical.Analysis.Real.Order.Strict.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace


LowerOpenHalfLinePredicate : ℝ → ℙ ℝ
LowerOpenHalfLinePredicate a x =
  (a <ℝ x) , isProp<ℝ a x

UpperOpenHalfLinePredicate : ℝ → ℙ ℝ
UpperOpenHalfLinePredicate b x =
  (x <ℝ b) , isProp<ℝ x b

OpenIntervalPredicate : ℝ → ℝ → ℙ ℝ
OpenIntervalPredicate a b =
  predicateIntersection
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)

isPropOpenIntervalMembership : ∀ a b x →
  isProp (x ∈ OpenIntervalPredicate a b)
isPropOpenIntervalMembership a b x =
  isProp× (isProp<ℝ a x) (isProp<ℝ x b)


LowerOpenHalfLine : ℝ → Type₀
LowerOpenHalfLine a =
  Σ[ x ∈ ℝ ] x ∈ LowerOpenHalfLinePredicate a

UpperOpenHalfLine : ℝ → Type₀
UpperOpenHalfLine b =
  Σ[ x ∈ ℝ ] x ∈ UpperOpenHalfLinePredicate b

OpenInterval : ℝ → ℝ → Type₀
OpenInterval a b =
  Σ[ x ∈ ℝ ] x ∈ OpenIntervalPredicate a b

isSetOpenInterval : ∀ a b → isSet (OpenInterval a b)
isSetOpenInterval a b =
  isSetΣSndProp isSetℝ (isPropOpenIntervalMembership a b)


LowerOpenHalfLinePremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
LowerOpenHalfLinePremetricSpace a =
  PremetricSubspace ℝPremetricSpace (LowerOpenHalfLinePredicate a)

UpperOpenHalfLinePremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
UpperOpenHalfLinePremetricSpace b =
  PremetricSubspace ℝPremetricSpace (UpperOpenHalfLinePredicate b)

OpenIntervalPremetricSpace :
  ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
OpenIntervalPremetricSpace a b =
  PremetricSubspace ℝPremetricSpace (OpenIntervalPredicate a b)


lowerOpenHalfLineInclusionNE : ∀ a →
  NE[ LowerOpenHalfLinePremetricSpace a , ℝPremetricSpace ]
lowerOpenHalfLineInclusionNE a =
  subspaceInclusionNE ℝPremetricSpace (LowerOpenHalfLinePredicate a)

upperOpenHalfLineInclusionNE : ∀ b →
  NE[ UpperOpenHalfLinePremetricSpace b , ℝPremetricSpace ]
upperOpenHalfLineInclusionNE b =
  subspaceInclusionNE ℝPremetricSpace (UpperOpenHalfLinePredicate b)

openIntervalInclusionNE : ∀ a b →
  NE[ OpenIntervalPremetricSpace a b , ℝPremetricSpace ]
openIntervalInclusionNE a b =
  subspaceInclusionNE ℝPremetricSpace (OpenIntervalPredicate a b)

openIntervalInclusionUC : ∀ a b →
  UC[ OpenIntervalPremetricSpace a b , ℝPremetricSpace ]
openIntervalInclusionUC a b =
  NE→UC (openIntervalInclusionNE a b)

openIntervalInclusionC : ∀ a b →
  C[ OpenIntervalPremetricSpace a b , ℝPremetricSpace ]
openIntervalInclusionC a b =
  NE→C (openIntervalInclusionNE a b)


private
  transportLeft≤ : ∀ {left right upper : ℝ} →
    left ≡ right → right ≤ℝ upper → left ≤ℝ upper
  transportLeft≤ {upper = upper} path =
    subst (λ (value : ℝ) → value ≤ℝ upper) (sym path)

  transportRight≤ : ∀ {left right upper : ℝ} →
    left ≡ right → left ≤ℝ upper → right ≤ℝ upper
  transportRight≤ {upper = upper} path =
    subst (λ (value : ℝ) → value ≤ℝ upper) path


private
  addCancelRPath : ∀ (x z : ℝ) →
    (x + z) + (- z) ≡ x
  addCancelRPath x z =
    sym (addAssoc x z (- z))
    ∙ cong (x +_) (addInvR z)
    ∙ addIdR x

  positiveGapHalfNeighbourAbove :
    ∀ a x y (gap : PositiveGap a x) →
    x ∼[ fst gap /2₊ ] y →
    a <ℝ y
  positiveGapHalfNeighbourAbove a x y gap x∼y =
    ∣ positiveGap {x = a} {y = y} half-width
        (≤ℝ-trans
          (a + half) (x - half) y
          half-gap-below-shifted-point
          (close→lowerBound y x half-width
            (sym∼ x y half-width x∼y))) ∣₁
    where
    half-width : ℚ₊
    half-width = fst gap /2₊

    half : ℝ
    half = rat (fst half-width)

    two-halves-path :
      (a + half) + half ≡ a + rat (fst (fst gap))
    two-halves-path =
      sym (addAssoc a half half)
      ∙ cong (a +_)
          (rat+rat (fst half-width) (fst half-width)
          ∙ cong rat (/2+/2≡id (fst (fst gap))))

    full-gap-bound :
      a + rat (fst (fst gap)) ≤ℝ x
    full-gap-bound =
      bound {x = a} {y = x} gap

    two-halves-below-x : (a + half) + half ≤ℝ x
    two-halves-below-x =
      transportLeft≤
        {left = (a + half) + half}
        {right = a + rat (fst (fst gap))}
        {upper = x}
        two-halves-path full-gap-bound

    half-gap-below-shifted-point : a + half ≤ℝ x - half
    half-gap-below-shifted-point =
      transportRight≤
        {left = ((a + half) + half) + (- half)}
        {right = a + half}
        {upper = x - half}
        (addCancelRPath (a + half) half)
        (addPres≤R ((a + half) + half) x (- half)
          two-halves-below-x)

  positiveGapHalfNeighbourBelow :
    ∀ x b y (gap : PositiveGap x b) →
    x ∼[ fst gap /2₊ ] y →
    y <ℝ b
  positiveGapHalfNeighbourBelow x b y gap x∼y =
    ∣ positiveGap {x = y} {y = b} half-width
        (≤ℝ-trans
          (y + half) ((x + half) + half) b
          (addPres≤R y (x + half) half
            (close→upperBound y x half-width
              (sym∼ x y half-width x∼y)))
          two-halves-below-b) ∣₁
    where
    half-width : ℚ₊
    half-width = fst gap /2₊

    half : ℝ
    half = rat (fst half-width)

    two-halves-path :
      (x + half) + half ≡ x + rat (fst (fst gap))
    two-halves-path =
      sym (addAssoc x half half)
      ∙ cong (x +_)
          (rat+rat (fst half-width) (fst half-width)
          ∙ cong rat (/2+/2≡id (fst (fst gap))))

    full-gap-bound :
      x + rat (fst (fst gap)) ≤ℝ b
    full-gap-bound =
      bound {x = x} {y = b} gap

    two-halves-below-b : (x + half) + half ≤ℝ b
    two-halves-below-b =
      transportLeft≤
        {left = (x + half) + half}
        {right = x + rat (fst (fst gap))}
        {upper = b}
        two-halves-path full-gap-bound


lowerOpenHalfLineIsOpen : ∀ a →
  IsOpenPredicate
    (ℝPremetricSpace .snd)
    (LowerOpenHalfLinePredicate a)
lowerOpenHalfLineIsOpen a x =
  PT.map λ gap →
    fst gap /2₊
    , λ y x∼y →
        positiveGapHalfNeighbourAbove a x y gap x∼y

upperOpenHalfLineIsOpen : ∀ b →
  IsOpenPredicate
    (ℝPremetricSpace .snd)
    (UpperOpenHalfLinePredicate b)
upperOpenHalfLineIsOpen b x =
  PT.map λ gap →
    fst gap /2₊
    , λ y x∼y →
        positiveGapHalfNeighbourBelow x b y gap x∼y

openIntervalIsOpen : ∀ a b →
  IsOpenPredicate
    (ℝPremetricSpace .snd)
    (OpenIntervalPredicate a b)
openIntervalIsOpen a b =
  intersectionIsOpen
    (ℝPremetricSpace .snd)
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)
    (lowerOpenHalfLineIsOpen a)
    (upperOpenHalfLineIsOpen b)
