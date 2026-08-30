module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.Dyadic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Equal
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Sequential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral


-- The abstract Riemann layer only needs a tagged partition scheme whose mesh
-- vanishes.  Equal dyadic partitions discharge that premise canonically on
-- every ordered interval, for either endpoint sampling convention.

dyadicLeftCauchyQuadrature : ∀ {a b f value} →
  (a≤b : a ≤ℝ b) →
  IsRiemannIntegral {a} {b} f value →
  CauchyQuadrature a b f
dyadicLeftCauchyQuadrature {a} {b} {f} {value} a≤b integral =
  riemannIntegralGivesCauchyQuadrature
    {a = a} {b = b} {f = f} {value = value}
    (dyadicLeftTaggedPartition a b a≤b)
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicRightCauchyQuadrature : ∀ {a b f value} →
  (a≤b : a ≤ℝ b) →
  IsRiemannIntegral {a} {b} f value →
  CauchyQuadrature a b f
dyadicRightCauchyQuadrature {a} {b} {f} {value} a≤b integral =
  riemannIntegralGivesCauchyQuadrature
    {a = a} {b = b} {f = f} {value = value}
    (dyadicRightTaggedPartition a b a≤b)
    (dyadicRightTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicMidpointCauchyQuadrature : ∀ {a b f value} →
  (a≤b : a ≤ℝ b) →
  IsRiemannIntegral {a} {b} f value →
  CauchyQuadrature a b f
dyadicMidpointCauchyQuadrature {a} {b} {f} {value} a≤b integral =
  riemannIntegralGivesCauchyQuadrature
    {a = a} {b = b} {f = f} {value = value}
    (dyadicMidpointTaggedPartition a b a≤b)
    (dyadicMidpointTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicLeftQuadratureValue : ∀ {a b f value}
  (a≤b : a ≤ℝ b)
  (integral : IsRiemannIntegral {a} {b} f value) →
  quadratureValue
    (dyadicLeftCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value} a≤b integral)
  ≡ value
dyadicLeftQuadratureValue {a} {b} {f} {value} a≤b integral =
  quadratureValueOfRiemannIntegral
    {a = a} {b = b} {f = f} {value = value}
    (dyadicLeftTaggedPartition a b a≤b)
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicRightQuadratureValue : ∀ {a b f value}
  (a≤b : a ≤ℝ b)
  (integral : IsRiemannIntegral {a} {b} f value) →
  quadratureValue
    (dyadicRightCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value} a≤b integral)
  ≡ value
dyadicRightQuadratureValue {a} {b} {f} {value} a≤b integral =
  quadratureValueOfRiemannIntegral
    {a = a} {b = b} {f = f} {value = value}
    (dyadicRightTaggedPartition a b a≤b)
    (dyadicRightTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicMidpointQuadratureValue : ∀ {a b f value}
  (a≤b : a ≤ℝ b)
  (integral : IsRiemannIntegral {a} {b} f value) →
  quadratureValue
    (dyadicMidpointCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value} a≤b integral)
  ≡ value
dyadicMidpointQuadratureValue {a} {b} {f} {value} a≤b integral =
  quadratureValueOfRiemannIntegral
    {a = a} {b = b} {f = f} {value = value}
    (dyadicMidpointTaggedPartition a b a≤b)
    (dyadicMidpointTaggedPartitionsHaveVanishingMesh a b a≤b)
    integral


dyadicEndpointQuadratureValuesAgree : ∀ {a b f value}
  (a≤b : a ≤ℝ b)
  (integral : IsRiemannIntegral {a} {b} f value) →
  quadratureValue
    (dyadicLeftCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value} a≤b integral)
  ≡
  quadratureValue
    (dyadicRightCauchyQuadrature
      {a = a} {b = b} {f = f} {value = value} a≤b integral)
dyadicEndpointQuadratureValuesAgree
  {a} {b} {f} {value} a≤b integral =
  dyadicLeftQuadratureValue
    {a = a} {b = b} {f = f} {value = value} a≤b integral
  ∙ sym (dyadicRightQuadratureValue
    {a = a} {b = b} {f = f} {value = value} a≤b integral)


-- In particular, uniqueness is unconditional once the interval ordering is
-- supplied.  The previous abstract theorem exposed a vanishing-mesh premise;
-- this version is the ordinary compact-interval statement clients need.

riemannIntegralUnique : ∀ {a b f x y} →
  a ≤ℝ b →
  IsRiemannIntegral {a} {b} f x →
  IsRiemannIntegral {a} {b} f y →
  x ≡ y
riemannIntegralUnique {a} {b} {f} {x} {y} a≤b =
  riemannIntegralUniqueAlongVanishingMesh
    {a = a} {b = b} {f = f} {x = x} {y = y}
    (dyadicLeftTaggedPartition a b a≤b)
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)


isPropRiemannIntegralWitness : ∀ {a b f} →
  (a≤b : a ≤ℝ b) →
  isProp (RiemannIntegralWitness {a} {b} f)
isPropRiemannIntegralWitness {a} {b} {f} a≤b =
  isPropRiemannIntegralWitnessAlongVanishingMesh
    {a = a} {b = b} {f = f}
    (dyadicLeftTaggedPartition a b a≤b)
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)


-- Mere existence can therefore be eliminated into the actual integral
-- witness without any countable choice.  Uniqueness, witnessed through the
-- concrete dyadic family, is precisely what makes this elimination safe.

canonicalRiemannIntegralWitness : ∀ {a b f} →
  (a≤b : a ≤ℝ b) →
  MerelyRiemannIntegrable {a} {b} f →
  RiemannIntegralWitness {a} {b} f
canonicalRiemannIntegralWitness {a} {b} {f} a≤b =
  extractRiemannIntegralWitness
    {a = a} {b = b} {f = f}
    (dyadicLeftTaggedPartition a b a≤b)
    (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)


canonicalRiemannIntegralValue : ∀ {a b f} →
  (a≤b : a ≤ℝ b) →
  MerelyRiemannIntegrable {a} {b} f →
  Real.ℝ
canonicalRiemannIntegralValue {a} {b} {f} a≤b integrable =
  fst (canonicalRiemannIntegralWitness
    {a = a} {b = b} {f = f} a≤b integrable)


canonicalRiemannIntegralValueIsIntegral : ∀ {a b f}
  (a≤b : a ≤ℝ b)
  (integrable : MerelyRiemannIntegrable {a} {b} f) →
  IsRiemannIntegral {a} {b} f
    (canonicalRiemannIntegralValue
      {a = a} {b = b} {f = f} a≤b integrable)
canonicalRiemannIntegralValueIsIntegral {a} {b} {f} a≤b integrable =
  snd (canonicalRiemannIntegralWitness
    {a = a} {b = b} {f = f} a≤b integrable)


canonicalRiemannIntegralValue-is-dyadic-left-limit : ∀ {a b f}
  (a≤b : a ≤ℝ b)
  (integrable : MerelyRiemannIntegrable {a} {b} f) →
  quadratureValue
    (dyadicLeftCauchyQuadrature
      {a = a} {b = b} {f = f}
      {value = canonicalRiemannIntegralValue
        {a = a} {b = b} {f = f} a≤b integrable}
      a≤b
      (canonicalRiemannIntegralValueIsIntegral
        {a = a} {b = b} {f = f} a≤b integrable))
  ≡ canonicalRiemannIntegralValue
      {a = a} {b = b} {f = f} a≤b integrable
canonicalRiemannIntegralValue-is-dyadic-left-limit
  {a} {b} {f} a≤b integrable =
  dyadicLeftQuadratureValue
    {a = a} {b = b} {f = f}
    {value = canonicalRiemannIntegralValue
      {a = a} {b = b} {f = f} a≤b integrable}
    a≤b
    (canonicalRiemannIntegralValueIsIntegral
      {a = a} {b = b} {f = f} a≤b integrable)


canonicalRiemannIntegralValue-is-dyadic-right-limit : ∀ {a b f}
  (a≤b : a ≤ℝ b)
  (integrable : MerelyRiemannIntegrable {a} {b} f) →
  quadratureValue
    (dyadicRightCauchyQuadrature
      {a = a} {b = b} {f = f}
      {value = canonicalRiemannIntegralValue
        {a = a} {b = b} {f = f} a≤b integrable}
      a≤b
      (canonicalRiemannIntegralValueIsIntegral
        {a = a} {b = b} {f = f} a≤b integrable))
  ≡ canonicalRiemannIntegralValue
      {a = a} {b = b} {f = f} a≤b integrable
canonicalRiemannIntegralValue-is-dyadic-right-limit
  {a} {b} {f} a≤b integrable =
  dyadicRightQuadratureValue
    {a = a} {b = b} {f = f}
    {value = canonicalRiemannIntegralValue
      {a = a} {b = b} {f = f} a≤b integrable}
    a≤b
    (canonicalRiemannIntegralValueIsIntegral
      {a = a} {b = b} {f = f} a≤b integrable)
