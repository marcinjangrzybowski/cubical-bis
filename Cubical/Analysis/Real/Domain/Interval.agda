module Cubical.Analysis.Real.Domain.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Completeness
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Lattice

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Subspace


ClosedIntervalPredicate : ℝ → ℝ → ℙ ℝ
ClosedIntervalPredicate a b x =
  ((a ≤ℝ x) × (x ≤ℝ b))
  , isProp× (isProp≤ℝ a x) (isProp≤ℝ x b)

isPropClosedIntervalMembership : ∀ a b x →
  isProp (x ∈ ClosedIntervalPredicate a b)
isPropClosedIntervalMembership a b x =
  isProp× (isProp≤ℝ a x) (isProp≤ℝ x b)

ClosedInterval : ℝ → ℝ → Type₀
ClosedInterval a b =
  Σ[ x ∈ ℝ ] x ∈ ClosedIntervalPredicate a b

isSetClosedInterval : ∀ a b → isSet (ClosedInterval a b)
isSetClosedInterval a b =
  isSetΣSndProp isSetℝ (isPropClosedIntervalMembership a b)


symmetricIntervalFromAbsBound : ∀ radius x →
  absℝ x ≤ℝ radius → ClosedInterval (- radius) radius
symmetricIntervalFromAbsBound radius x bounded =
  x
  , subst ((- radius) ≤ℝ_) (negInvol x)
      (negPres≤ (- x) radius
        (≤ℝ-trans (- x) (absℝ x) radius (negLeAbs x) bounded))
  , ≤ℝ-trans x (absℝ x) radius (leAbs x) bounded


ClosedIntervalPremetricSpace :
  ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedIntervalPremetricSpace a b =
  PremetricSubspace ℝPremetricSpace (ClosedIntervalPredicate a b)


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


-- The endpoint order proof is needed only to show that the result lies in
-- the interval.  The underlying clamp is non-expanding for every a and b.

clampInterval : ℝ → ℝ → ℝ → ℝ
clampInterval a b x = maxℝ a (minℝ b x)

clampIntervalLowerBound : ∀ a b x →
  a ≤ℝ clampInterval a b x
clampIntervalLowerBound a b x =
  left≤max a (minℝ b x)

clampIntervalUpperBound : ∀ a b →
  a ≤ℝ b →
  ∀ x → clampInterval a b x ≤ℝ b
clampIntervalUpperBound a b a≤b x =
  maxLeastUpperBound a (minℝ b x) b
    a≤b (min≤left b x)

clampIntervalPres∼ : ∀ a b x y ε →
  x ∼[ ε ] y →
  clampInterval a b x ∼[ ε ] clampInterval a b y
clampIntervalPres∼ a b x y ε x∼y =
  max-isNonExpanding₂ a .IsNonExpanding.pres≈
    (minℝ b x) (minℝ b y) ε
    (min-isNonExpanding₂ b .IsNonExpanding.pres≈
      x y ε x∼y)

clampIntervalIsNonExpanding : ∀ a b →
  IsNonExpanding
    (ℝPremetricSpace .snd) (clampInterval a b)
    (ℝPremetricSpace .snd)
clampIntervalIsNonExpanding a b .IsNonExpanding.pres≈ =
  clampIntervalPres∼ a b


private
  minUpperFix : ∀ x b →
    x ≤ℝ b → minℝ b x ≡ x
  minUpperFix x b x≤b =
    cong -_ (negPres≤ x b x≤b)
    ∙ negInvol x


clampIntervalFix : ∀ a b x →
  a ≤ℝ x → x ≤ℝ b →
  clampInterval a b x ≡ x
clampIntervalFix a b x a≤x x≤b =
  cong (maxℝ a) (minUpperFix x b x≤b)
  ∙ a≤x


clampIntervalRetractionNE : ∀ a b →
  a ≤ℝ b →
  NE[ ℝPremetricSpace , ClosedIntervalPremetricSpace a b ]
fst (clampIntervalRetractionNE a b a≤b) x =
  clampInterval a b x
  , clampIntervalLowerBound a b x
  , clampIntervalUpperBound a b a≤b x
IsNonExpanding.pres≈
  (snd (clampIntervalRetractionNE a b a≤b)) =
  clampIntervalPres∼ a b

clampIntervalRetractionSection : ∀ a b →
  (a≤b : a ≤ℝ b) →
  ∀ point →
  fst (clampIntervalRetractionNE a b a≤b)
      (fst (closedIntervalInclusionNE a b) point)
    ≡ point
clampIntervalRetractionSection a b a≤b point =
  Σ≡Prop
    (isPropClosedIntervalMembership a b)
    (clampIntervalFix a b (fst point)
      (fst (snd point)) (snd (snd point)))


closedIntervalIsComplete : ∀ a b →
  a ≤ℝ b →
  PremetricTheory.isComplete (ClosedIntervalPremetricSpace a b)
closedIntervalIsComplete a b a≤b =
  retractPresIsComplete
    isCompleteℝ
    (closedIntervalInclusionNE a b)
    (clampIntervalRetractionNE a b a≤b)
    (clampIntervalRetractionSection a b a≤b)


UnitInterval : Type₀
UnitInterval = ClosedInterval 0ℝ 1ℝ

UnitIntervalPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
UnitIntervalPremetricSpace = ClosedIntervalPremetricSpace 0ℝ 1ℝ
