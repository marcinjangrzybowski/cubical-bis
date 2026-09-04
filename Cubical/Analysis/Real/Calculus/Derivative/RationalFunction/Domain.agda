module Cubical.Analysis.Real.Calculus.Derivative.RationalFunction.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness


-- The natural constructive domain of a denominator is its apartness locus.
-- Apartness supplies the quantitative sign information consumed by the
-- signed inverse, while proof irrelevance keeps this a genuine subspace.

ApartDenominatorPredicate : (ℝ → ℝ) → ℙ ℝ
ApartDenominatorPredicate denominator x =
  (0ℝ #ℝ denominator x) , isProp#ℝ 0ℝ (denominator x)


ApartDenominatorDomain : (ℝ → ℝ) → Type
ApartDenominatorDomain denominator =
  Σ[ x ∈ ℝ ] x ∈ ApartDenominatorPredicate denominator


ApartDenominatorDomainPremetricSpace :
  (denominator : ℝ → ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
ApartDenominatorDomainPremetricSpace denominator =
  PremetricSubspace
    ℝPremetricSpace
    (ApartDenominatorPredicate denominator)


apartDenominatorDomainCoordinate :
  ∀ {denominator} →
  ApartDenominatorDomain denominator → ℝ
apartDenominatorDomainCoordinate = fst


apartDenominatorDomainCoordinateIsContinuous :
  ∀ denominator →
  isContinuous
    (ApartDenominatorDomainPremetricSpace denominator .snd)
    apartDenominatorDomainCoordinate
    (ℝPremetricSpace .snd)
apartDenominatorDomainCoordinateIsContinuous denominator =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace
        (ApartDenominatorPredicate denominator)))


mapApartDenominatorDomain :
  ∀ source-denominator target-denominator →
  (∀ x →
    0ℝ #ℝ source-denominator x →
    0ℝ #ℝ target-denominator x) →
  ApartDenominatorDomain source-denominator →
  ApartDenominatorDomain target-denominator
mapApartDenominatorDomain
  source-denominator target-denominator
  preserves-apart point =
    fst point
    , preserves-apart (fst point) (snd point)


mapApartDenominatorDomain-coordinate :
  ∀ source-denominator target-denominator preserves-apart point →
  apartDenominatorDomainCoordinate
      (mapApartDenominatorDomain
        source-denominator target-denominator
        preserves-apart point)
    ≡
  apartDenominatorDomainCoordinate point
mapApartDenominatorDomain-coordinate
  source-denominator target-denominator
  preserves-apart point =
    refl


mapApartDenominatorDomainNE :
  ∀ source-denominator target-denominator →
  (preserves-apart :
    ∀ x →
      0ℝ #ℝ source-denominator x →
      0ℝ #ℝ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
fst
  (mapApartDenominatorDomainNE
    source-denominator target-denominator
    preserves-apart) =
      mapApartDenominatorDomain
        source-denominator target-denominator
        preserves-apart
IsNonExpanding.pres≈
  (snd
    (mapApartDenominatorDomainNE
      source-denominator target-denominator
      preserves-apart))
  point other ε =
    idfun _


mapApartDenominatorDomainC :
  ∀ source-denominator target-denominator →
  (preserves-apart :
    ∀ x →
      0ℝ #ℝ source-denominator x →
      0ℝ #ℝ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainC
  source-denominator target-denominator
  preserves-apart =
    NE→C
      (mapApartDenominatorDomainNE
        source-denominator target-denominator
        preserves-apart)


mapApartDenominatorDomainByPath :
  ∀ source-denominator target-denominator →
  (∀ x →
    source-denominator x ≡ target-denominator x) →
  ApartDenominatorDomain source-denominator →
  ApartDenominatorDomain target-denominator
mapApartDenominatorDomainByPath
  source-denominator target-denominator
  denominator-path =
    mapApartDenominatorDomain
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → 0ℝ #ℝ value)
          (denominator-path x)
          source-apart)


mapApartDenominatorDomainByPathNE :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x →
      source-denominator x ≡ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainByPathNE
  source-denominator target-denominator
  denominator-path =
    mapApartDenominatorDomainNE
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → 0ℝ #ℝ value)
          (denominator-path x)
          source-apart)


mapApartDenominatorDomainByPathC :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x →
      source-denominator x ≡ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainByPathC
  source-denominator target-denominator
  denominator-path =
    NE→C
      (mapApartDenominatorDomainByPathNE
        source-denominator target-denominator
        denominator-path)


mapApartDenominatorDomainByPath-roundtrip :
  ∀ source-denominator target-denominator
    (denominator-path :
      ∀ x →
        source-denominator x ≡ target-denominator x)
    point →
  mapApartDenominatorDomainByPath
      target-denominator source-denominator
      (λ x → sym (denominator-path x))
      (mapApartDenominatorDomainByPath
        source-denominator target-denominator
        denominator-path point)
    ≡
  point
mapApartDenominatorDomainByPath-roundtrip
  source-denominator target-denominator
  denominator-path point =
    Σ≡Prop
      (λ x → isProp#ℝ 0ℝ (source-denominator x))
      refl


restrictToApartDenominatorDomain :
  ∀ {denominator} →
  (ℝ → ℝ) →
  ApartDenominatorDomain denominator → ℝ
restrictToApartDenominatorDomain function point =
  function (fst point)


apartDenominatorDomainMap :
  ∀ denominator →
  ApartDenominatorDomain denominator →
  Σ[ value ∈ ℝ ] 0ℝ #ℝ value
apartDenominatorDomainMap denominator point =
  denominator (fst point) , snd point


divideOnApartDenominatorDomain :
  (numerator denominator : ℝ → ℝ) →
  ApartDenominatorDomain denominator → ℝ
divideOnApartDenominatorDomain numerator denominator point =
  divideℝ
    (numerator (fst point))
    (denominator (fst point))
    (snd point)


divideOnApartDenominatorDomain-proofIrrelevant :
  ∀ numerator denominator x
    (left right : 0ℝ #ℝ denominator x) →
  divideOnApartDenominatorDomain numerator denominator (x , left)
    ≡
  divideOnApartDenominatorDomain numerator denominator (x , right)
divideOnApartDenominatorDomain-proofIrrelevant
  numerator denominator x left right =
    cong
      (numerator x ·_)
      (inverseℝProofIrrelevant
        (denominator x) left right)
