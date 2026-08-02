module Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Located

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

LowerClosedHalfLinePredicate : ℝ → ℙ ℝ
LowerClosedHalfLinePredicate a x =
  (a ≤ℝ x) , isProp≤ℝ a x

UpperClosedHalfLinePredicate : ℝ → ℙ ℝ
UpperClosedHalfLinePredicate b x =
  (x ≤ℝ b) , isProp≤ℝ x b

OpenIntervalPredicate : ℝ → ℝ → ℙ ℝ
OpenIntervalPredicate a b =
  predicateIntersection
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)

ClosedIntervalPredicate : ℝ → ℝ → ℙ ℝ
ClosedIntervalPredicate a b x =
  ((a ≤ℝ x) × (x ≤ℝ b))
  , isProp× (isProp≤ℝ a x) (isProp≤ℝ x b)

LeftOpenRightClosedIntervalPredicate : ℝ → ℝ → ℙ ℝ
LeftOpenRightClosedIntervalPredicate a b x =
  ((a <ℝ x) × (x ≤ℝ b))
  , isProp× (isProp<ℝ a x) (isProp≤ℝ x b)

OpenInterval : ℝ → ℝ → Type
OpenInterval a b =
  Σ[ x ∈ ℝ ] x ∈ OpenIntervalPredicate a b

ClosedInterval : ℝ → ℝ → Type
ClosedInterval a b =
  Σ[ x ∈ ℝ ] x ∈ ClosedIntervalPredicate a b

LeftOpenRightClosedInterval : ℝ → ℝ → Type
LeftOpenRightClosedInterval a b =
  Σ[ x ∈ ℝ ] x ∈ LeftOpenRightClosedIntervalPredicate a b

LowerOpenHalfLine : ℝ → Type
LowerOpenHalfLine a =
  Σ[ x ∈ ℝ ] x ∈ LowerOpenHalfLinePredicate a

LowerClosedHalfLine : ℝ → Type
LowerClosedHalfLine a =
  Σ[ x ∈ ℝ ] x ∈ LowerClosedHalfLinePredicate a

UpperClosedHalfLine : ℝ → Type
UpperClosedHalfLine b =
  Σ[ x ∈ ℝ ] x ∈ UpperClosedHalfLinePredicate b

OpenIntervalPremetricSpace : ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
OpenIntervalPremetricSpace a b =
  PremetricSubspace ℝPremetricSpace (OpenIntervalPredicate a b)

ClosedIntervalPremetricSpace : ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedIntervalPremetricSpace a b =
  PremetricSubspace ℝPremetricSpace (ClosedIntervalPredicate a b)

LeftOpenRightClosedIntervalPremetricSpace :
  ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
LeftOpenRightClosedIntervalPremetricSpace a b =
  PremetricSubspace
    ℝPremetricSpace
    (LeftOpenRightClosedIntervalPredicate a b)

LowerOpenHalfLinePremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
LowerOpenHalfLinePremetricSpace a =
  PremetricSubspace ℝPremetricSpace (LowerOpenHalfLinePredicate a)

LowerClosedHalfLinePremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
LowerClosedHalfLinePremetricSpace a =
  PremetricSubspace ℝPremetricSpace (LowerClosedHalfLinePredicate a)

UpperClosedHalfLinePremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
UpperClosedHalfLinePremetricSpace b =
  PremetricSubspace ℝPremetricSpace (UpperClosedHalfLinePredicate b)

UnitInterval : Type
UnitInterval = ClosedInterval 0 1

UnitIntervalPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
UnitIntervalPremetricSpace = ClosedIntervalPremetricSpace 0 1

closedIntervalInclusionNE : ∀ a b →
  NE[ ClosedIntervalPremetricSpace a b , ℝPremetricSpace ]
closedIntervalInclusionNE a b =
  subspaceInclusionNE ℝPremetricSpace (ClosedIntervalPredicate a b)

closedIntervalInclusionUC : ∀ a b →
  UC[ ClosedIntervalPremetricSpace a b , ℝPremetricSpace ]
closedIntervalInclusionUC a b =
  NE→UC (closedIntervalInclusionNE a b)

closedIntervalInclusionC : ∀ a b →
  C[ ClosedIntervalPremetricSpace a b , ℝPremetricSpace ]
closedIntervalInclusionC a b =
  NE→C (closedIntervalInclusionNE a b)

lowerClosedHalfLineInclusionNE : ∀ a →
  NE[ LowerClosedHalfLinePremetricSpace a , ℝPremetricSpace ]
lowerClosedHalfLineInclusionNE a =
  subspaceInclusionNE ℝPremetricSpace (LowerClosedHalfLinePredicate a)

upperClosedHalfLineInclusionNE : ∀ b →
  NE[ UpperClosedHalfLinePremetricSpace b , ℝPremetricSpace ]
upperClosedHalfLineInclusionNE b =
  subspaceInclusionNE ℝPremetricSpace (UpperClosedHalfLinePredicate b)

lowerOpenHalfLineInclusionNE : ∀ a →
  NE[ LowerOpenHalfLinePremetricSpace a , ℝPremetricSpace ]
lowerOpenHalfLineInclusionNE a =
  subspaceInclusionNE ℝPremetricSpace (LowerOpenHalfLinePredicate a)

maxToLowerClosedHalfLineNE : ∀ a →
  NE[ ℝPremetricSpace , LowerClosedHalfLinePremetricSpace a ]
fst (maxToLowerClosedHalfLineNE a) x =
  maxℝ a x , left≤max a x
IsNonExpanding.pres≈ (snd (maxToLowerClosedHalfLineNE a))
  x y ε =
    maxPres∼₂ a x y ε

minToUpperClosedHalfLineNE : ∀ b →
  NE[ ℝPremetricSpace , UpperClosedHalfLinePremetricSpace b ]
fst (minToUpperClosedHalfLineNE b) x =
  minℝ b x , min≤left b x
IsNonExpanding.pres≈ (snd (minToUpperClosedHalfLineNE b))
  x y ε =
    minPres∼₂ b x y ε

maxToLowerClosedHalfLineSection : ∀ a point →
  fst (maxToLowerClosedHalfLineNE a)
      (fst (lowerClosedHalfLineInclusionNE a) point)
    ≡ point
maxToLowerClosedHalfLineSection a point =
  Σ≡Prop
    (isProp≤ℝ a)
    (maxOf≤ a (fst point) (snd point))

minToUpperClosedHalfLineSection : ∀ b point →
  fst (minToUpperClosedHalfLineNE b)
      (fst (upperClosedHalfLineInclusionNE b) point)
    ≡ point
minToUpperClosedHalfLineSection b point =
  Σ≡Prop
    (λ x → isProp≤ℝ x b)
    (minComm b (fst point)
    ∙ minOf≤ (fst point) b (snd point))

-- Clamp only the lower endpoint of an upper half-line.  The upper bound is
-- inherited from the source; dually, the second map clamps only the upper
-- endpoint of a lower half-line.  These are the retractions needed when a
-- bounded piece is pasted to an unbounded one.
lowerClampToClosedIntervalNE : ∀ a b →
  a ≤ℝ b →
  NE[ UpperClosedHalfLinePremetricSpace b
    , ClosedIntervalPremetricSpace a b ]
fst (lowerClampToClosedIntervalNE a b a≤b) point =
  maxℝ a (fst point)
  , left≤max a (fst point)
  , max≤ a (fst point) b a≤b (snd point)
IsNonExpanding.pres≈ (snd (lowerClampToClosedIntervalNE a b a≤b))
  point other ε point∼other =
    maxPres∼₂ a (fst point) (fst other) ε point∼other

upperClampToClosedIntervalNE : ∀ a b →
  a ≤ℝ b →
  NE[ LowerClosedHalfLinePremetricSpace a
    , ClosedIntervalPremetricSpace a b ]
fst (upperClampToClosedIntervalNE a b a≤b) point =
  minℝ b (fst point)
  , ≤min a b (fst point) a≤b (snd point)
  , min≤left b (fst point)
IsNonExpanding.pres≈ (snd (upperClampToClosedIntervalNE a b a≤b))
  point other ε point∼other =
    minPres∼₂ b (fst point) (fst other) ε point∼other

lowerClampToClosedIntervalSection : ∀ a b →
  (a≤b : a ≤ℝ b) →
  ∀ point →
  fst (lowerClampToClosedIntervalNE a b a≤b)
      (fst point , snd (snd point))
    ≡ point
lowerClampToClosedIntervalSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (maxOf≤ a (fst point) (fst (snd point)))

upperClampToClosedIntervalSection : ∀ a b →
  (a≤b : a ≤ℝ b) →
  ∀ point →
  fst (upperClampToClosedIntervalNE a b a≤b)
      (fst point , fst (snd point))
    ≡ point
upperClampToClosedIntervalSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (minComm b (fst point)
    ∙ minOf≤ (fst point) b (snd (snd point)))

minToLeftOpenRightClosedIntervalNE : ∀ a b →
  a <ℝ b →
  NE[ LowerOpenHalfLinePremetricSpace a
    , LeftOpenRightClosedIntervalPremetricSpace a b ]
fst (minToLeftOpenRightClosedIntervalNE a b a<b) point =
  minℝ b (fst point)
  , minStrictLower b (fst point) a a<b (snd point)
  , min≤left b (fst point)
IsNonExpanding.pres≈
  (snd (minToLeftOpenRightClosedIntervalNE a b a<b))
  point other ε point∼other =
    minPres∼₂ b (fst point) (fst other) ε point∼other

maxFromLowerOpenToLowerClosedHalfLineNE : ∀ a b →
  NE[ LowerOpenHalfLinePremetricSpace a
    , LowerClosedHalfLinePremetricSpace b ]
fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) point =
  maxℝ b (fst point) , left≤max b (fst point)
IsNonExpanding.pres≈
  (snd (maxFromLowerOpenToLowerClosedHalfLineNE a b))
  point other ε point∼other =
    maxPres∼₂ b (fst point) (fst other) ε point∼other

minToLeftOpenRightClosedIntervalSection : ∀ a b →
  (a<b : a <ℝ b) →
  ∀ point →
  fst (minToLeftOpenRightClosedIntervalNE a b a<b)
      (fst point , fst (snd point))
    ≡ point
minToLeftOpenRightClosedIntervalSection a b a<b point =
  Σ≡Prop
    (λ x → isProp× (isProp<ℝ a x) (isProp≤ℝ x b))
    (minComm b (fst point)
    ∙ minOf≤ (fst point) b (snd (snd point)))

minToLeftOpenRightClosedIntervalOnRight : ∀ a b →
  (a<b : a <ℝ b) →
  ∀ x (a<x : a <ℝ x) (b≤x : b ≤ℝ x) →
  fst (minToLeftOpenRightClosedIntervalNE a b a<b) (x , a<x)
    ≡ (b , a<b , ≤ℝ-refl b)
minToLeftOpenRightClosedIntervalOnRight a b a<b x a<x b≤x =
  Σ≡Prop
    (λ y → isProp× (isProp<ℝ a y) (isProp≤ℝ y b))
    (minOf≤ b x b≤x)

maxFromLowerOpenToLowerClosedHalfLineOnRight : ∀ a b x →
  (a<x : a <ℝ x) →
  (b≤x : b ≤ℝ x) →
  fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) (x , a<x)
    ≡ (x , b≤x)
maxFromLowerOpenToLowerClosedHalfLineOnRight a b x a<x b≤x =
  Σ≡Prop
    (isProp≤ℝ b)
    (maxOf≤ b x b≤x)

maxFromLowerOpenToLowerClosedHalfLineOnLeft : ∀ a b x →
  (a<x : a <ℝ x) →
  (x≤b : x ≤ℝ b) →
  fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) (x , a<x)
    ≡ (b , ≤ℝ-refl b)
maxFromLowerOpenToLowerClosedHalfLineOnLeft a b x a<x x≤b =
  Σ≡Prop
    (isProp≤ℝ b)
    (maxComm b x ∙ maxOf≤ x b x≤b)

private
  positiveGapHalfNeighbourAbove :
    ∀ a x y (gap : PositiveGap a x) →
    x ∼[ width gap /2₊ ] y →
    a <ℝ y
  positiveGapHalfNeighbourAbove a x y gap x∼y =
    ∣ positiveGap half-width
        (gapBoundIntro a y half-width
          (≤ℝ-trans
            (a + half) (x - half) y
            half-gap-below-shifted-point
            (close→lowerBound y x half-width
              (sym∼ x y half-width x∼y)))) ∣₁
    where
    half-width : ℚ₊
    half-width = width gap /2₊

    half : ℝ
    half = rat (fst half-width)

    two-halves-path :
      (a + half) + half ≡ a + rat (fst (width gap))
    two-halves-path =
      sym (addAssoc a half half)
      ∙ cong (a +_)
          (rat+rat (fst half-width) (fst half-width)
          ∙ cong rat
              (1/2∈ℚ./2+/2≡id (fst (width gap))))

    two-halves-below-x : (a + half) + half ≤ℝ x
    two-halves-below-x =
      subst (_≤ℝ x) (sym two-halves-path)
        (gapBoundElim a x (width gap) (bound gap))

    half-gap-below-shifted-point : a + half ≤ℝ x - half
    half-gap-below-shifted-point =
      subst2 _≤ℝ_
        (addSubCancel (a + half) half)
        refl
        (≤ℝ-addR
          ((a + half) + half) x (- half)
          two-halves-below-x)

  positiveGapHalfNeighbourBelow :
    ∀ x b y (gap : PositiveGap x b) →
    x ∼[ width gap /2₊ ] y →
    y <ℝ b
  positiveGapHalfNeighbourBelow x b y gap x∼y =
    ∣ positiveGap half-width
        (gapBoundIntro y b half-width
          (≤ℝ-trans
            (y + half) ((x + half) + half) b
            (≤ℝ-addR y (x + half) half
              (close→upperBound y x half-width
                (sym∼ x y half-width x∼y)))
            two-halves-below-b)) ∣₁
    where
    half-width : ℚ₊
    half-width = width gap /2₊

    half : ℝ
    half = rat (fst half-width)

    two-halves-path :
      (x + half) + half ≡ x + rat (fst (width gap))
    two-halves-path =
      sym (addAssoc x half half)
      ∙ cong (x +_)
          (rat+rat (fst half-width) (fst half-width)
          ∙ cong rat
              (1/2∈ℚ./2+/2≡id (fst (width gap))))

    two-halves-below-b : (x + half) + half ≤ℝ b
    two-halves-below-b =
      subst (_≤ℝ b) (sym two-halves-path)
        (gapBoundElim x b (width gap) (bound gap))

lowerOpenHalfLineIsOpen : ∀ a →
  IsOpenPredicate
    (snd ℝPremetricSpace)
    (LowerOpenHalfLinePredicate a)
lowerOpenHalfLineIsOpen a x =
  PT.map λ gap →
    width gap /2₊
    , λ y x∼y → positiveGapHalfNeighbourAbove a x y gap x∼y

upperOpenHalfLineIsOpen : ∀ b →
  IsOpenPredicate
    (snd ℝPremetricSpace)
    (UpperOpenHalfLinePredicate b)
upperOpenHalfLineIsOpen b x =
  PT.map λ gap →
    width gap /2₊
    , λ y x∼y → positiveGapHalfNeighbourBelow x b y gap x∼y

openIntervalIsOpen : ∀ a b →
  IsOpenPredicate
    (snd ℝPremetricSpace)
    (OpenIntervalPredicate a b)
openIntervalIsOpen a b =
  intersectionIsOpen
    (snd ℝPremetricSpace)
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)
    (lowerOpenHalfLineIsOpen a)
    (upperOpenHalfLineIsOpen b)

openInterval⊆closedInterval : ∀ a b →
  OpenIntervalPredicate a b ⊆ ClosedIntervalPredicate a b
openInterval⊆closedInterval a b x (a<x , x<b) =
  <ℝ-weaken a x a<x
  , <ℝ-weaken x b x<b

clampIntervalRetractionNE : ∀ a b →
  a ≤ℝ b →
  NE[ ℝPremetricSpace , ClosedIntervalPremetricSpace a b ]
fst (clampIntervalRetractionNE a b a≤b) x =
  clampInterval a b x
  , clampIntervalLowerBound a b a≤b x
  , clampIntervalUpperBound a b x
IsNonExpanding.pres≈ (snd (clampIntervalRetractionNE a b a≤b))
  x y ε =
    clampIntervalPres∼ a b x y ε

clampIntervalRetractionSection : ∀ a b →
  (a≤b : a ≤ℝ b) →
  ∀ point →
  fst (clampIntervalRetractionNE a b a≤b)
      (fst (closedIntervalInclusionNE a b) point)
    ≡ point
clampIntervalRetractionSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (clampIntervalFixpoint a b (fst point)
      (fst (snd point)) (snd (snd point)))
