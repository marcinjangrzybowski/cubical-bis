module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Sequential


-- The Riemann condition keeps the choice of a sufficiently small mesh under
-- truncation separately at each error radius.  Its body is a proposition, so
-- this witness can be opened wherever a convergence or equality proof needs
-- it; no global modulus of integrability is assembled.

IsRiemannIntegral : ∀ {a b} →
  (Real.ℝ → Real.ℝ) → Real.ℝ → Type₀
IsRiemannIntegral {a} {b} f value =
  ∀ ε →
    ∃[ δ ∈ ℚ₊ ]
      (∀ (tagged : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
        riemannSum tagged f Real.Base.≈ᶜ[ ε ] value)


isPropIsRiemannIntegral : ∀ {a b} f value →
  isProp (IsRiemannIntegral {a} {b} f value)
isPropIsRiemannIntegral f value =
  isPropΠ λ _ → squash₁


-- This is the main bridge from the partition definition to the native
-- sequential completion.  Both existential choices are eliminated only into
-- the truncated tail demanded by `isLimitSequence`.

riemannIntegralAlongVanishingMesh : ∀ {a b f value}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  IsRiemannIntegral f value →
  isLimitSequence (quadratureSequence partitions f) value
riemannIntegralAlongVanishingMesh {a} {b} {f} {value}
  partitions mesh→zero integral ε =
  PT.rec squash₁ use-integral-radius (integral ε)
  where
  use-integral-radius :
    Σ[ δ ∈ ℚ₊ ]
      (∀ (tagged : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
        riemannSum tagged f Real.Base.≈ᶜ[ ε ] value) →
    ∃[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        quadratureSequence partitions f n Real.Base.≈ᶜ[ ε ] value)
  use-integral-radius (δ , fine-sum-close) =
    PT.map
      (λ { (N , fine-tail) →
        N , λ n N≤n →
          fine-sum-close (partitions n) (fine-tail n N≤n) })
      (mesh→zero δ)


riemannIntegralGivesCauchyQuadrature : ∀ {a b f value}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  IsRiemannIntegral f value →
  CauchyQuadrature a b f
riemannIntegralGivesCauchyQuadrature {a} {b} {f} {value}
  partitions mesh→zero integral
  .CauchyQuadrature.partitions = partitions
riemannIntegralGivesCauchyQuadrature {a} {b} {f} {value}
  partitions mesh→zero integral
  .CauchyQuadrature.sumsCauchy =
  isLimitSequence→isCauchySequence
    (riemannIntegralAlongVanishingMesh
      {a = a} {b = b} {f = f} {value = value}
      partitions mesh→zero integral)


quadratureValueOfRiemannIntegral : ∀ {a b f value}
  (partitions : ℕ → TaggedPartition[ a , b ])
  (mesh→zero : HasVanishingMesh partitions)
  (integral : IsRiemannIntegral f value) →
  quadratureValue
    (riemannIntegralGivesCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value}
      partitions mesh→zero integral) ≡ value
quadratureValueOfRiemannIntegral {a} {b} {f = f} {value = value}
  partitions mesh→zero integral =
  canonicalLimit≡
    (quadratureSequence partitions f)
    (CauchyQuadrature.sumsCauchy
      (riemannIntegralGivesCauchyQuadrature
        {a = a} {b = b} {f = f} {value = value}
        partitions mesh→zero integral))
    value
    (riemannIntegralAlongVanishingMesh
      {a = a} {b = b} {f = f} {value = value}
      partitions mesh→zero integral)


-- Uniqueness is deliberately stated relative to one vanishing-mesh scheme.
-- Without the existence of arbitrarily fine partitions the universal Riemann
-- condition could be vacuous.  A canonical dyadic scheme will discharge this
-- geometric premise for ordinary intervals.

riemannIntegralUniqueAlongVanishingMesh : ∀ {a b f x y}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  IsRiemannIntegral f x →
  IsRiemannIntegral f y →
  x ≡ y
riemannIntegralUniqueAlongVanishingMesh {a} {b} {f = f} {x = x} {y = y}
  partitions mesh→zero integral-x integral-y =
  sym value-x ∙ value-y
  where
  qx : CauchyQuadrature a b f
  qx = riemannIntegralGivesCauchyQuadrature
    {a = a} {b = b} {f = f} {value = x}
    partitions mesh→zero integral-x

  value-x : quadratureValue qx ≡ x
  value-x = quadratureValueOfRiemannIntegral
    {a = a} {b = b} {f = f} {value = x}
    partitions mesh→zero integral-x

  value-y : quadratureValue qx ≡ y
  value-y = canonicalLimit≡
    (quadratureSequence partitions f)
    (CauchyQuadrature.sumsCauchy qx)
    y
    (riemannIntegralAlongVanishingMesh
      {a = a} {b = b} {f = f} {value = y}
      partitions mesh→zero integral-y)


-- Once an interval has one vanishing-mesh scheme, a value together with its
-- Riemann condition is a proposition: the value is unique and the condition
-- is proposition-valued.  Consequently *mere* integrability can be promoted
-- to an actual value-and-proof pair.  This is a safe use of truncation which
-- gains information from uniqueness, rather than choosing representatives.

RiemannIntegralWitness : ∀ {a b} →
  (Real.ℝ → Real.ℝ) → Type₀
RiemannIntegralWitness {a} {b} f =
  Σ[ value ∈ Real.ℝ ] IsRiemannIntegral {a} {b} f value


MerelyRiemannIntegrable : ∀ {a b} →
  (Real.ℝ → Real.ℝ) → Type₀
MerelyRiemannIntegrable {a} {b} f =
  ∥ RiemannIntegralWitness {a} {b} f ∥₁


isPropRiemannIntegralWitnessAlongVanishingMesh : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  isProp (RiemannIntegralWitness {a} {b} f)
isPropRiemannIntegralWitnessAlongVanishingMesh
  {a} {b} {f = f}
  partitions mesh→zero (x , integral-x) (y , integral-y) =
  Σ≡Prop
    (isPropIsRiemannIntegral f)
    (riemannIntegralUniqueAlongVanishingMesh
      {a = a} {b = b} {f = f} {x = x} {y = y}
      partitions mesh→zero integral-x integral-y)


extractRiemannIntegralWitness : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  MerelyRiemannIntegrable {a} {b} f →
  RiemannIntegralWitness {a} {b} f
extractRiemannIntegralWitness {a} {b} {f = f}
  partitions mesh→zero =
  PT.rec
    (isPropRiemannIntegralWitnessAlongVanishingMesh
      {a = a} {b = b} {f = f}
      partitions mesh→zero)
    (λ witness → witness)


integralValue : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  MerelyRiemannIntegrable {a} {b} f →
  Real.ℝ
integralValue {a} {b} {f = f}
  partitions mesh→zero integrable =
  fst (extractRiemannIntegralWitness
    {a = a} {b = b} {f = f}
    partitions mesh→zero integrable)


integralValueIsRiemannIntegral : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ])
  (mesh→zero : HasVanishingMesh partitions)
  (integrable : MerelyRiemannIntegrable {a} {b} f) →
  IsRiemannIntegral {a} {b} f
    (integralValue {a = a} {b = b} {f = f}
      partitions mesh→zero integrable)
integralValueIsRiemannIntegral {a} {b} {f = f}
  partitions mesh→zero integrable =
  snd (extractRiemannIntegralWitness
    {a = a} {b = b} {f = f}
    partitions mesh→zero integrable)


-- The scheme is needed to justify untruncation, but it is not part of the
-- mathematical value.  Two different vanishing-mesh schemes extract equal
-- reals, even when the input supplies only mere integrability.

integralValueIndependentOfScheme : ∀ {a b f}
  (left right : ℕ → TaggedPartition[ a , b ])
  (left-mesh→zero : HasVanishingMesh left)
  (right-mesh→zero : HasVanishingMesh right)
  (integrable : MerelyRiemannIntegrable {a} {b} f) →
  integralValue {a = a} {b = b} {f = f}
    left left-mesh→zero integrable
  ≡
  integralValue {a = a} {b = b} {f = f}
    right right-mesh→zero integrable
integralValueIndependentOfScheme {a} {b} {f = f}
  left right left-mesh→zero right-mesh→zero integrable =
  riemannIntegralUniqueAlongVanishingMesh
    {a = a} {b = b} {f = f}
    {x = integralValue {a = a} {b = b} {f = f}
      left left-mesh→zero integrable}
    {y = integralValue {a = a} {b = b} {f = f}
      right right-mesh→zero integrable}
    left left-mesh→zero
    (integralValueIsRiemannIntegral
      {a = a} {b = b} {f = f}
      left left-mesh→zero integrable)
    (integralValueIsRiemannIntegral
      {a = a} {b = b} {f = f}
      right right-mesh→zero integrable)
