module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Quotient
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.SignedReciprocal


-- The natural constructive domain of a denominator is its apartness locus.
-- This is stronger than negated equality and is exactly the information
-- consumed by signed inversion.  Because apartness is a proposition, the
-- domain remains a genuine subspace rather than a space with computationally
-- relevant duplicate points.

ApartDenominatorPredicate : (Real.ℝ → Real.ℝ) → ℙ Real.ℝ
ApartDenominatorPredicate denominator x =
  0＃ₚ (denominator x)


ApartDenominatorDomain : (Real.ℝ → Real.ℝ) → Type
ApartDenominatorDomain denominator =
  Σ[ x ∈ Real.ℝ ] x ∈ ApartDenominatorPredicate denominator


ApartDenominatorDomainPremetricSpace :
  (denominator : Real.ℝ → Real.ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
ApartDenominatorDomainPremetricSpace denominator =
  PremetricSubspace
    Real.ℝPremetricSpace
    (ApartDenominatorPredicate denominator)


apartDenominatorDomainCoordinate :
  ∀ {denominator} →
  ApartDenominatorDomain denominator → Real.ℝ
apartDenominatorDomainCoordinate = fst


apartDenominatorDomainCoordinateIsContinuous :
  ∀ denominator →
  isContinuous
    (snd (ApartDenominatorDomainPremetricSpace denominator))
    apartDenominatorDomainCoordinate
    (snd Real.ℝPremetricSpace)
apartDenominatorDomainCoordinateIsContinuous denominator =
  snd
    (NE→C
      (subspaceInclusionNE
        Real.ℝPremetricSpace
        (ApartDenominatorPredicate denominator)))


-- This is stronger than the corresponding bare subspace construction for
-- the comparison reals: continuity of the denominator already makes its
-- natural apartness domain open.  No uniform gap from zero is chosen.

apartDenominatorPredicateIsOpen :
  ∀ denominator →
  isContinuous
    (snd Real.ℝPremetricSpace) denominator
    (snd Real.ℝPremetricSpace) →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (ApartDenominatorPredicate denominator)
apartDenominatorPredicateIsOpen denominator denominator-continuous =
  continuousPreimageIsOpen
    denominator ApartRealPredicate
    denominator-continuous
    apartRealPredicateIsOpen


apartDenominatorPredicateOfDerivativeIsOpen :
  ∀ denominator denominator-derivative →
  IsDerivative denominator denominator-derivative →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (ApartDenominatorPredicate denominator)
apartDenominatorPredicateOfDerivativeIsOpen
  denominator denominator-derivative denominator-has-derivative =
    apartDenominatorPredicateIsOpen denominator
      (derivativeIsContinuous
        denominator denominator-derivative
        denominator-has-derivative)


mapApartDenominatorDomain :
  ∀ source-denominator target-denominator →
  (∀ x →
    Real.ιℚ 0 ＃ source-denominator x →
    Real.ιℚ 0 ＃ target-denominator x) →
  ApartDenominatorDomain source-denominator →
  ApartDenominatorDomain target-denominator
mapApartDenominatorDomain
  source-denominator target-denominator preserves-apart point =
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
  source-denominator target-denominator preserves-apart point =
    refl


mapApartDenominatorDomainNE :
  ∀ source-denominator target-denominator →
  (preserves-apart :
    ∀ x →
      Real.ιℚ 0 ＃ source-denominator x →
      Real.ιℚ 0 ＃ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
fst
  (mapApartDenominatorDomainNE
    source-denominator target-denominator preserves-apart) =
      mapApartDenominatorDomain
        source-denominator target-denominator preserves-apart
IsNonExpanding.pres≈
  (snd
    (mapApartDenominatorDomainNE
      source-denominator target-denominator preserves-apart))
  point other ε =
    idfun _


mapApartDenominatorDomainC :
  ∀ source-denominator target-denominator →
  (preserves-apart :
    ∀ x →
      Real.ιℚ 0 ＃ source-denominator x →
      Real.ιℚ 0 ＃ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainC
  source-denominator target-denominator preserves-apart =
    NE→C
      (mapApartDenominatorDomainNE
        source-denominator target-denominator preserves-apart)


mapApartDenominatorDomainByPath :
  ∀ source-denominator target-denominator →
  (∀ x → source-denominator x ≡ target-denominator x) →
  ApartDenominatorDomain source-denominator →
  ApartDenominatorDomain target-denominator
mapApartDenominatorDomainByPath
  source-denominator target-denominator denominator-path =
    mapApartDenominatorDomain
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → Real.ιℚ 0 ＃ value)
          (denominator-path x)
          source-apart)


mapApartDenominatorDomainByPathNE :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x → source-denominator x ≡ target-denominator x) →
  NE[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainByPathNE
  source-denominator target-denominator denominator-path =
    mapApartDenominatorDomainNE
      source-denominator target-denominator
      (λ x source-apart →
        subst
          (λ value → Real.ιℚ 0 ＃ value)
          (denominator-path x)
          source-apart)


mapApartDenominatorDomainByPathC :
  ∀ source-denominator target-denominator →
  (denominator-path :
    ∀ x → source-denominator x ≡ target-denominator x) →
  C[
    ApartDenominatorDomainPremetricSpace source-denominator
    ,
    ApartDenominatorDomainPremetricSpace target-denominator
  ]
mapApartDenominatorDomainByPathC
  source-denominator target-denominator denominator-path =
    NE→C
      (mapApartDenominatorDomainByPathNE
        source-denominator target-denominator denominator-path)


mapApartDenominatorDomainByPath-roundtrip :
  ∀ source-denominator target-denominator
    (denominator-path :
      ∀ x → source-denominator x ≡ target-denominator x)
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
  source-denominator target-denominator denominator-path point =
    Σ≡Prop
      (λ x → isProp＃ (Real.ιℚ 0) (source-denominator x))
      refl


restrictToApartDenominatorDomain :
  ∀ {denominator} →
  (Real.ℝ → Real.ℝ) →
  ApartDenominatorDomain denominator → Real.ℝ
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
      (snd Real.ℝPremetricSpace)
      (idfun Real.ℝ) function derivative fst
      (apartDenominatorDomainCoordinateIsContinuous denominator)
      has-derivative


apartDenominatorDomainMap :
  ∀ denominator →
  ApartDenominatorDomain denominator → ApartReal
apartDenominatorDomainMap denominator point =
  denominator (fst point) , snd point


divideOnApartDenominatorDomain :
  (numerator denominator : Real.ℝ → Real.ℝ) →
  ApartDenominatorDomain denominator → Real.ℝ
divideOnApartDenominatorDomain numerator denominator point =
  divideℝ
    (numerator (fst point))
    (denominator (fst point))
    (snd point)


-- The normalized quotient-rule value uses two copies of the already
-- constructed reciprocal.  It has the conventional numerator f'g - fg'
-- while avoiding normalization of a proof-indexed inverse of g².

divideOnApartDenominatorDomainDerivative :
  (numerator denominator
   numerator-derivative denominator-derivative :
    Real.ℝ → Real.ℝ) →
  ApartDenominatorDomain denominator → Real.ℝ
divideOnApartDenominatorDomainDerivative
  numerator denominator
  numerator-derivative denominator-derivative =
    quotientRuleNormalizedDerivative
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      (λ point → snd point)
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)


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
    divideByApartDenominatorHasNormalizedDerivativeAlong
      (snd (ApartDenominatorDomainPremetricSpace denominator))
      apartDenominatorDomainCoordinate
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      (λ point → snd point)
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)
      (apartDenominatorDomainCoordinateIsContinuous denominator)
      (restrictHasDerivativeToApartDenominatorDomain
        denominator numerator numerator-derivative
        numerator-has-derivative)
      (restrictHasDerivativeToApartDenominatorDomain
        denominator denominator denominator-derivative
        denominator-has-derivative)


-- Any total extension agreeing with the partial quotient inherits the
-- expected ordinary derivative at every point of the natural domain.  The
-- openness witness and the denominator gap both remain truncated/local.

divideOnApartDenominatorDomainDerivativeAtWithExtension :
  ∀ numerator denominator
    numerator-derivative denominator-derivative extension →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  (∀ point →
    extension (fst point) ≡
      divideOnApartDenominatorDomain numerator denominator point) →
  ∀ x →
  (x-apart : Real.ιℚ 0 ＃ denominator x) →
  IsDerivativeAt
    extension
    (divideOnApartDenominatorDomainDerivative
      numerator denominator
      numerator-derivative denominator-derivative
      (x , x-apart))
    x
divideOnApartDenominatorDomainDerivativeAtWithExtension
  numerator denominator
  numerator-derivative denominator-derivative extension
  numerator-has-derivative denominator-has-derivative agrees
  x x-apart =
    openSubspaceDerivativeAtWithExtension
      (ApartDenominatorPredicate denominator)
      (apartDenominatorPredicateOfDerivativeIsOpen
        denominator denominator-derivative
        denominator-has-derivative)
      (divideOnApartDenominatorDomain numerator denominator)
      (divideOnApartDenominatorDomainDerivative
        numerator denominator
        numerator-derivative denominator-derivative)
      extension
      (divideOnApartDenominatorDomainHasDerivativeAlong
        numerator denominator
        numerator-derivative denominator-derivative
        numerator-has-derivative denominator-has-derivative)
      agrees x x-apart


-- In particular, changing the apartness witness never changes the value of
-- either the partial quotient or its derivative.

divideOnApartDenominatorDomain-proofIrrelevant :
  ∀ numerator denominator x
    (left right : Real.ιℚ 0 ＃ denominator x) →
  divideOnApartDenominatorDomain numerator denominator (x , left)
    ≡
  divideOnApartDenominatorDomain numerator denominator (x , right)
divideOnApartDenominatorDomain-proofIrrelevant
  numerator denominator x left right =
    cong
      (divideOnApartDenominatorDomain numerator denominator)
      (pair-path left right)
  where
  pair-path : ∀ left right →
    (x , left) ≡ (x , right)
  pair-path left right =
    ΣPathP
      (refl
      , isProp＃ (Real.ιℚ 0) (denominator x) left right)


divideOnApartDenominatorDomainDerivative-proofIrrelevant :
  ∀ numerator denominator
    numerator-derivative denominator-derivative x
    (left right : Real.ιℚ 0 ＃ denominator x) →
  divideOnApartDenominatorDomainDerivative
      numerator denominator
      numerator-derivative denominator-derivative
      (x , left)
    ≡
  divideOnApartDenominatorDomainDerivative
      numerator denominator
      numerator-derivative denominator-derivative
      (x , right)
divideOnApartDenominatorDomainDerivative-proofIrrelevant
  numerator denominator numerator-derivative denominator-derivative
  x left right =
    cong
      (divideOnApartDenominatorDomainDerivative
        numerator denominator
        numerator-derivative denominator-derivative)
      (pair-path left right)
  where
  pair-path : ∀ left right →
    (x , left) ≡ (x , right)
  pair-path left right =
    ΣPathP
      (refl
      , isProp＃ (Real.ιℚ 0) (denominator x) left right)
