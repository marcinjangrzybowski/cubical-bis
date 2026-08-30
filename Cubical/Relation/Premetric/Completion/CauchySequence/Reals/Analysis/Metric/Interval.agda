module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Located
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Clamp
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order


LowerOpenHalfLinePredicate : Real.ℝ → ℙ Real.ℝ
LowerOpenHalfLinePredicate a x =
  (a <ℝ x) , isProp<ℝ a x


UpperOpenHalfLinePredicate : Real.ℝ → ℙ Real.ℝ
UpperOpenHalfLinePredicate b x =
  (x <ℝ b) , isProp<ℝ x b


LowerClosedHalfLinePredicate : Real.ℝ → ℙ Real.ℝ
LowerClosedHalfLinePredicate a x =
  (a ≤ℝ x) , isProp≤ℝ a x


UpperClosedHalfLinePredicate : Real.ℝ → ℙ Real.ℝ
UpperClosedHalfLinePredicate b x =
  (x ≤ℝ b) , isProp≤ℝ x b


OpenIntervalPredicate : Real.ℝ → Real.ℝ → ℙ Real.ℝ
OpenIntervalPredicate a b =
  predicateIntersection
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)


ClosedIntervalPredicate : Real.ℝ → Real.ℝ → ℙ Real.ℝ
ClosedIntervalPredicate a b x =
  ((a ≤ℝ x) × (x ≤ℝ b))
  , isProp× (isProp≤ℝ a x) (isProp≤ℝ x b)


LeftOpenRightClosedIntervalPredicate :
  Real.ℝ → Real.ℝ → ℙ Real.ℝ
LeftOpenRightClosedIntervalPredicate a b x =
  ((a <ℝ x) × (x ≤ℝ b))
  , isProp× (isProp<ℝ a x) (isProp≤ℝ x b)


OpenInterval : Real.ℝ → Real.ℝ → Type₀
OpenInterval a b =
  Σ[ x ∈ Real.ℝ ] x ∈ OpenIntervalPredicate a b


ClosedInterval : Real.ℝ → Real.ℝ → Type₀
ClosedInterval a b =
  Σ[ x ∈ Real.ℝ ] x ∈ ClosedIntervalPredicate a b


LeftOpenRightClosedInterval : Real.ℝ → Real.ℝ → Type₀
LeftOpenRightClosedInterval a b =
  Σ[ x ∈ Real.ℝ ] x ∈ LeftOpenRightClosedIntervalPredicate a b


LowerOpenHalfLine : Real.ℝ → Type₀
LowerOpenHalfLine a =
  Σ[ x ∈ Real.ℝ ] x ∈ LowerOpenHalfLinePredicate a


LowerClosedHalfLine : Real.ℝ → Type₀
LowerClosedHalfLine a =
  Σ[ x ∈ Real.ℝ ] x ∈ LowerClosedHalfLinePredicate a


UpperClosedHalfLine : Real.ℝ → Type₀
UpperClosedHalfLine b =
  Σ[ x ∈ Real.ℝ ] x ∈ UpperClosedHalfLinePredicate b


OpenIntervalPremetricSpace :
  Real.ℝ → Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
OpenIntervalPremetricSpace a b =
  PremetricSubspace Real.ℝPremetricSpace (OpenIntervalPredicate a b)


ClosedIntervalPremetricSpace :
  Real.ℝ → Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedIntervalPremetricSpace a b =
  PremetricSubspace Real.ℝPremetricSpace (ClosedIntervalPredicate a b)


LeftOpenRightClosedIntervalPremetricSpace :
  Real.ℝ → Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
LeftOpenRightClosedIntervalPremetricSpace a b =
  PremetricSubspace Real.ℝPremetricSpace
    (LeftOpenRightClosedIntervalPredicate a b)


LowerOpenHalfLinePremetricSpace :
  Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
LowerOpenHalfLinePremetricSpace a =
  PremetricSubspace Real.ℝPremetricSpace (LowerOpenHalfLinePredicate a)


LowerClosedHalfLinePremetricSpace :
  Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
LowerClosedHalfLinePremetricSpace a =
  PremetricSubspace Real.ℝPremetricSpace (LowerClosedHalfLinePredicate a)


UpperClosedHalfLinePremetricSpace :
  Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
UpperClosedHalfLinePremetricSpace b =
  PremetricSubspace Real.ℝPremetricSpace (UpperClosedHalfLinePredicate b)


UnitInterval : Type₀
UnitInterval = ClosedInterval (Real.ιℚ 0) (Real.ιℚ 1)


UnitIntervalPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
UnitIntervalPremetricSpace =
  ClosedIntervalPremetricSpace (Real.ιℚ 0) (Real.ιℚ 1)


closedIntervalInclusionNE : ∀ a b →
  NE[ ClosedIntervalPremetricSpace a b , Real.ℝPremetricSpace ]
closedIntervalInclusionNE a b =
  subspaceInclusionNE Real.ℝPremetricSpace (ClosedIntervalPredicate a b)


closedIntervalInclusionUC : ∀ a b →
  UC[ ClosedIntervalPremetricSpace a b , Real.ℝPremetricSpace ]
closedIntervalInclusionUC a b =
  NE→UC (closedIntervalInclusionNE a b)


closedIntervalInclusionC : ∀ a b →
  C[ ClosedIntervalPremetricSpace a b , Real.ℝPremetricSpace ]
closedIntervalInclusionC a b =
  NE→C (closedIntervalInclusionNE a b)


lowerClosedHalfLineInclusionNE : ∀ a →
  NE[ LowerClosedHalfLinePremetricSpace a , Real.ℝPremetricSpace ]
lowerClosedHalfLineInclusionNE a =
  subspaceInclusionNE Real.ℝPremetricSpace
    (LowerClosedHalfLinePredicate a)


upperClosedHalfLineInclusionNE : ∀ b →
  NE[ UpperClosedHalfLinePremetricSpace b , Real.ℝPremetricSpace ]
upperClosedHalfLineInclusionNE b =
  subspaceInclusionNE Real.ℝPremetricSpace
    (UpperClosedHalfLinePredicate b)


lowerOpenHalfLineInclusionNE : ∀ a →
  NE[ LowerOpenHalfLinePremetricSpace a , Real.ℝPremetricSpace ]
lowerOpenHalfLineInclusionNE a =
  subspaceInclusionNE Real.ℝPremetricSpace
    (LowerOpenHalfLinePredicate a)


maxToLowerClosedHalfLineNE : ∀ a →
  NE[ Real.ℝPremetricSpace , LowerClosedHalfLinePremetricSpace a ]
fst (maxToLowerClosedHalfLineNE a) x =
  a ⊔ℝ x , max-upper-left a x
IsNonExpanding.pres≈ (snd (maxToLowerClosedHalfLineNE a)) x y ε =
  max-pres≈₂ a x y ε


minToUpperClosedHalfLineNE : ∀ b →
  NE[ Real.ℝPremetricSpace , UpperClosedHalfLinePremetricSpace b ]
fst (minToUpperClosedHalfLineNE b) x =
  b ⊓ℝ x , min-lower-left b x
IsNonExpanding.pres≈ (snd (minToUpperClosedHalfLineNE b)) x y ε =
  min-pres≈₂ b x y ε


maxToLowerClosedHalfLineSection : ∀ a point →
  fst (maxToLowerClosedHalfLineNE a)
      (fst (lowerClosedHalfLineInclusionNE a) point) ≡ point
maxToLowerClosedHalfLineSection a point =
  Σ≡Prop (isProp≤ℝ a) (snd point)


minToUpperClosedHalfLineSection : ∀ b point →
  fst (minToUpperClosedHalfLineNE b)
      (fst (upperClosedHalfLineInclusionNE b) point) ≡ point
minToUpperClosedHalfLineSection b point =
  Σ≡Prop (λ x → isProp≤ℝ x b)
    (min-comm b (fst point) ∙ ≤ℝ→min (fst point) b (snd point))


lowerClampToClosedIntervalNE : ∀ a b →
  a ≤ℝ b →
  NE[ UpperClosedHalfLinePremetricSpace b
    , ClosedIntervalPremetricSpace a b ]
fst (lowerClampToClosedIntervalNE a b a≤b) point =
  a ⊔ℝ fst point
  , max-upper-left a (fst point)
  , max-least a (fst point) b a≤b (snd point)
IsNonExpanding.pres≈ (snd (lowerClampToClosedIntervalNE a b a≤b))
  point other ε =
  max-pres≈₂ a (fst point) (fst other) ε


upperClampToClosedIntervalNE : ∀ a b →
  a ≤ℝ b →
  NE[ LowerClosedHalfLinePremetricSpace a
    , ClosedIntervalPremetricSpace a b ]
fst (upperClampToClosedIntervalNE a b a≤b) point =
  b ⊓ℝ fst point
  , min-greatest b (fst point) a a≤b (snd point)
  , min-lower-left b (fst point)
IsNonExpanding.pres≈ (snd (upperClampToClosedIntervalNE a b a≤b))
  point other ε =
  min-pres≈₂ b (fst point) (fst other) ε


lowerClampToClosedIntervalSection : ∀ a b →
  (a≤b : a ≤ℝ b) → ∀ point →
  fst (lowerClampToClosedIntervalNE a b a≤b)
      (fst point , snd (snd point)) ≡ point
lowerClampToClosedIntervalSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (fst (snd point))


upperClampToClosedIntervalSection : ∀ a b →
  (a≤b : a ≤ℝ b) → ∀ point →
  fst (upperClampToClosedIntervalNE a b a≤b)
      (fst point , fst (snd point)) ≡ point
upperClampToClosedIntervalSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (min-comm b (fst point)
    ∙ ≤ℝ→min (fst point) b (snd (snd point)))


minToLeftOpenRightClosedIntervalNE : ∀ a b →
  a <ℝ b →
  NE[ LowerOpenHalfLinePremetricSpace a
    , LeftOpenRightClosedIntervalPremetricSpace a b ]
fst (minToLeftOpenRightClosedIntervalNE a b a<b) point =
  b ⊓ℝ fst point
  , minPositiveStrictLower b (fst point) a a<b (snd point)
  , min-lower-left b (fst point)
IsNonExpanding.pres≈
  (snd (minToLeftOpenRightClosedIntervalNE a b a<b))
  point other ε =
  min-pres≈₂ b (fst point) (fst other) ε


maxFromLowerOpenToLowerClosedHalfLineNE : ∀ a b →
  NE[ LowerOpenHalfLinePremetricSpace a
    , LowerClosedHalfLinePremetricSpace b ]
fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) point =
  b ⊔ℝ fst point , max-upper-left b (fst point)
IsNonExpanding.pres≈
  (snd (maxFromLowerOpenToLowerClosedHalfLineNE a b))
  point other ε =
  max-pres≈₂ b (fst point) (fst other) ε


minToLeftOpenRightClosedIntervalSection : ∀ a b →
  (a<b : a <ℝ b) → ∀ point →
  fst (minToLeftOpenRightClosedIntervalNE a b a<b)
      (fst point , fst (snd point)) ≡ point
minToLeftOpenRightClosedIntervalSection a b a<b point =
  Σ≡Prop
    (λ x → isProp× (isProp<ℝ a x) (isProp≤ℝ x b))
    (min-comm b (fst point)
    ∙ ≤ℝ→min (fst point) b (snd (snd point)))


minToLeftOpenRightClosedIntervalOnRight : ∀ a b →
  (a<b : a <ℝ b) → ∀ x →
  (a<x : a <ℝ x) → (b≤x : b ≤ℝ x) →
  fst (minToLeftOpenRightClosedIntervalNE a b a<b) (x , a<x) ≡
    (b , a<b , ≤ℝ-refl b)
minToLeftOpenRightClosedIntervalOnRight a b a<b x a<x b≤x =
  Σ≡Prop
    (λ y → isProp× (isProp<ℝ a y) (isProp≤ℝ y b))
    (≤ℝ→min b x b≤x)


maxFromLowerOpenToLowerClosedHalfLineOnRight : ∀ a b x →
  (a<x : a <ℝ x) → (b≤x : b ≤ℝ x) →
  fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) (x , a<x) ≡
    (x , b≤x)
maxFromLowerOpenToLowerClosedHalfLineOnRight a b x a<x b≤x =
  Σ≡Prop (isProp≤ℝ b) b≤x


maxFromLowerOpenToLowerClosedHalfLineOnLeft : ∀ a b x →
  (a<x : a <ℝ x) → (x≤b : x ≤ℝ b) →
  fst (maxFromLowerOpenToLowerClosedHalfLineNE a b) (x , a<x) ≡
    (b , ≤ℝ-refl b)
maxFromLowerOpenToLowerClosedHalfLineOnLeft a b x a<x x≤b =
  Σ≡Prop (isProp≤ℝ b)
    (max-comm b x ∙ x≤b)


clampIntervalRetractionNE : ∀ a b →
  a ≤ℝ b →
  NE[ Real.ℝPremetricSpace , ClosedIntervalPremetricSpace a b ]
fst (clampIntervalRetractionNE a b a≤b) x =
  clampInterval a b x
  , clampIntervalLowerBound a b a≤b x
  , clampIntervalUpperBound a b x
IsNonExpanding.pres≈ (snd (clampIntervalRetractionNE a b a≤b))
  x y ε =
  clampInterval-pres≈ a b x y ε


clampIntervalRetractionSection : ∀ a b →
  (a≤b : a ≤ℝ b) → ∀ point →
  fst (clampIntervalRetractionNE a b a≤b)
      (fst (closedIntervalInclusionNE a b) point) ≡ point
clampIntervalRetractionSection a b a≤b point =
  Σ≡Prop
    (λ x → isProp× (isProp≤ℝ a x) (isProp≤ℝ x b))
    (clampIntervalFixpoint a b (fst point)
      (fst (snd point)) (snd (snd point)))


-- Downstream extension proofs need the section only propositionally.  This
-- opaque interface prevents elaboration from normalising the full lattice
-- formula for max/min every time the section is used under congruence.
opaque
  canonicalClosedIntervalRetractionNE : ∀ a b →
    a ≤ℝ b →
    NE[ Real.ℝPremetricSpace , ClosedIntervalPremetricSpace a b ]
  canonicalClosedIntervalRetractionNE = clampIntervalRetractionNE

  canonicalClosedIntervalRetractionSection : ∀ a b →
    (a≤b : a ≤ℝ b) → ∀ point →
    fst (canonicalClosedIntervalRetractionNE a b a≤b)
        (fst (closedIntervalInclusionNE a b) point) ≡ point
  canonicalClosedIntervalRetractionSection =
    clampIntervalRetractionSection


-- Strict membership contains a rational gap.  Halving that gap gives an
-- open metric neighbourhood, but the gap is opened only underneath the
-- propositional truncation which already defines strict order.

private
  positiveGapHalfNeighbourAbove :
    ∀ a x y (gap : PositiveGap a x) →
    x Real.Base.≈ᶜ[ width gap /2₊ ] y →
    a <ℝ y
  positiveGapHalfNeighbourAbove a x y gap x≈y =
    ∣ positiveGap half-width
        (≤ℝ-trans (a Add.+ half) (x Group.- half) y
          half-gap-below-shifted-point
          (close→lowerBound y x half-width
            (Real.Base.sym≈ᶜ x y half-width x≈y))) ∣₁
    where
    half-width : ℚ₊
    half-width = width gap /2₊

    half : Real.ℝ
    half = Real.ιℚ (fst half-width)

    two-halves-path :
      (a Add.+ half) Add.+ half ≡
      a Add.+ Real.ιℚ (fst (width gap))
    two-halves-path =
      sym (add-assoc a half half)
      ∙ cong (a Add.+_)
          (Add.add-ι-ι (fst half-width) (fst half-width)
          ∙ cong Real.ιℚ (/2+/2≡id (fst (width gap))))

    two-halves-below-x : (a Add.+ half) Add.+ half ≤ℝ x
    two-halves-below-x =
      subst (_≤ℝ x) (sym two-halves-path) (bound gap)

    half-gap-below-shifted-point :
      a Add.+ half ≤ℝ x Group.- half
    half-gap-below-shifted-point =
      subst2 _≤ℝ_
        (add-sub-cancel (a Add.+ half) half) refl
        (add-preserves≤-right
          ((a Add.+ half) Add.+ half) x (Neg.- half)
          two-halves-below-x)


  positiveGapHalfNeighbourBelow :
    ∀ x b y (gap : PositiveGap x b) →
    x Real.Base.≈ᶜ[ width gap /2₊ ] y →
    y <ℝ b
  positiveGapHalfNeighbourBelow x b y gap x≈y =
    ∣ positiveGap half-width
        (≤ℝ-trans (y Add.+ half) ((x Add.+ half) Add.+ half) b
          (add-preserves≤-right y (x Add.+ half) half
            (close→upperBound y x half-width
              (Real.Base.sym≈ᶜ x y half-width x≈y)))
          two-halves-below-b) ∣₁
    where
    half-width : ℚ₊
    half-width = width gap /2₊

    half : Real.ℝ
    half = Real.ιℚ (fst half-width)

    two-halves-path :
      (x Add.+ half) Add.+ half ≡
      x Add.+ Real.ιℚ (fst (width gap))
    two-halves-path =
      sym (add-assoc x half half)
      ∙ cong (x Add.+_)
          (Add.add-ι-ι (fst half-width) (fst half-width)
          ∙ cong Real.ιℚ (/2+/2≡id (fst (width gap))))

    two-halves-below-b : (x Add.+ half) Add.+ half ≤ℝ b
    two-halves-below-b =
      subst (_≤ℝ b) (sym two-halves-path) (bound gap)


lowerOpenHalfLineIsOpen : ∀ a →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (LowerOpenHalfLinePredicate a)
lowerOpenHalfLineIsOpen a x =
  PT.map λ gap →
    width gap /2₊
    , λ y x≈y → positiveGapHalfNeighbourAbove a x y gap x≈y


upperOpenHalfLineIsOpen : ∀ b →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (UpperOpenHalfLinePredicate b)
upperOpenHalfLineIsOpen b x =
  PT.map λ gap →
    width gap /2₊
    , λ y x≈y → positiveGapHalfNeighbourBelow x b y gap x≈y


openIntervalIsOpen : ∀ a b →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (OpenIntervalPredicate a b)
openIntervalIsOpen a b =
  intersectionIsOpen
    (snd Real.ℝPremetricSpace)
    (LowerOpenHalfLinePredicate a)
    (UpperOpenHalfLinePredicate b)
    (lowerOpenHalfLineIsOpen a)
    (upperOpenHalfLineIsOpen b)


openInterval⊆closedInterval : ∀ a b →
  OpenIntervalPredicate a b ⊆ ClosedIntervalPredicate a b
openInterval⊆closedInterval a b x (a<x , x<b) =
  <ℝ-weaken a x a<x , <ℝ-weaken x b x<b
