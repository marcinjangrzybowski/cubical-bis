module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Quotient
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.SignedReciprocal

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

-- The natural constructive domain of a real denominator consists of the
-- points where its value carries positive apartness information.  This is
-- stronger than mere inequality and is exactly the evidence required by
-- signed inversion.
ApartDenominatorPredicate : (ℝ → ℝ) → ℙ ℝ
ApartDenominatorPredicate denominator x =
  0＃ₚ (denominator x)

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
    (snd (ApartDenominatorDomainPremetricSpace denominator))
    apartDenominatorDomainCoordinate
    (snd ℝPremetricSpace)
apartDenominatorDomainCoordinateIsContinuous denominator =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace
        (ApartDenominatorPredicate denominator)))

mapApartDenominatorDomain :
  ∀ source-denominator target-denominator →
  (∀ x →
    0 ＃ source-denominator x →
    0 ＃ target-denominator x) →
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
      0 ＃ source-denominator x →
      0 ＃ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace
      source-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      target-denominator
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
      0 ＃ source-denominator x →
      0 ＃ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace
      source-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      target-denominator
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
    source-denominator x
      ≡ target-denominator x) →
  ApartDenominatorDomain source-denominator →
  ApartDenominatorDomain target-denominator
mapApartDenominatorDomainByPath
  source-denominator target-denominator
  denominator-path =
    mapApartDenominatorDomain
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → 0 ＃ value)
          (denominator-path x)
          source-apart)

mapApartDenominatorDomainByPathNE :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x →
      source-denominator x
        ≡ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace
      source-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      target-denominator
    ]
mapApartDenominatorDomainByPathNE
  source-denominator target-denominator
  denominator-path =
    mapApartDenominatorDomainNE
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → 0 ＃ value)
          (denominator-path x)
          source-apart)

mapApartDenominatorDomainByPathC :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x →
      source-denominator x
        ≡ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace
      source-denominator
    ,
    ApartDenominatorDomainPremetricSpace
      target-denominator
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
        source-denominator x
          ≡ target-denominator x)
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
      (λ x →
        isProp＃ 0 (source-denominator x))
      refl

restrictToApartDenominatorDomain :
  ∀ {denominator} →
  (ℝ → ℝ) →
  ApartDenominatorDomain denominator → ℝ
restrictToApartDenominatorDomain function point =
  function (fst point)

restrictHasDerivativeToApartDenominatorDomain :
  ∀ denominator function derivative →
  IsDerivative function derivative →
  IsDerivativeAlong
    (snd (ApartDenominatorDomainPremetricSpace denominator))
    apartDenominatorDomainCoordinate
    (restrictToApartDenominatorDomain function)
    (restrictToApartDenominatorDomain derivative)
restrictHasDerivativeToApartDenominatorDomain
  denominator function derivative has-derivative =
    pullbackHasDerivativeAlong
      (snd (ApartDenominatorDomainPremetricSpace denominator))
      (snd ℝPremetricSpace)
      (idfun ℝ) function derivative fst
      (apartDenominatorDomainCoordinateIsContinuous denominator)
      has-derivative

apartDenominatorDomainMap :
  ∀ denominator →
  ApartDenominatorDomain denominator → ApartReal
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

divideOnApartDenominatorDomainDerivative :
  (numerator denominator
   numerator-derivative denominator-derivative : ℝ → ℝ) →
  ApartDenominatorDomain denominator → ℝ
divideOnApartDenominatorDomainDerivative
  numerator denominator
  numerator-derivative denominator-derivative point =
    divideByApartDenominatorDerivative
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      (central-proof denominator)
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)
      point
  where
  central-proof :
    ∀ denominator point →
    0 ＃ restrictToApartDenominatorDomain denominator point
  central-proof denominator point = snd point

divideOnApartDenominatorDomainHasDerivativeAlong :
  ∀ numerator denominator
    numerator-derivative denominator-derivative →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivativeAlong
    (snd (ApartDenominatorDomainPremetricSpace denominator))
    apartDenominatorDomainCoordinate
    (divideOnApartDenominatorDomain numerator denominator)
    (divideOnApartDenominatorDomainDerivative
      numerator denominator
      numerator-derivative denominator-derivative)
divideOnApartDenominatorDomainHasDerivativeAlong
  numerator denominator
  numerator-derivative denominator-derivative
  numerator-has-derivative denominator-has-derivative =
    divideByApartDenominatorHasDerivativeAlong
      (snd (ApartDenominatorDomainPremetricSpace denominator))
      apartDenominatorDomainCoordinate
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      central-proof
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)
      (apartDenominatorDomainCoordinateIsContinuous denominator)
      (restrictHasDerivativeToApartDenominatorDomain
        denominator numerator numerator-derivative
        numerator-has-derivative)
      (restrictHasDerivativeToApartDenominatorDomain
        denominator denominator denominator-derivative
        denominator-has-derivative)
  where
  central-proof :
    ∀ point →
    0 ＃ restrictToApartDenominatorDomain denominator point
  central-proof point = snd point
