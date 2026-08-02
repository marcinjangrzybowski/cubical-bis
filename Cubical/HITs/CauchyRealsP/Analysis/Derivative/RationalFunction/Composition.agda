module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Chain
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

-- Composition has two independent constructive domain obligations.  The
-- inner denominator must be apart from zero at the original coordinate, and
-- the outer denominator must be apart from zero at the value of the inner
-- quotient.  Keeping the second obligation as a subspace of the first makes
-- that dependency explicit.
RationalCompositionPredicate :
  (inner-numerator inner-denominator outer-denominator : ℝ → ℝ) →
  ℙ (ApartDenominatorDomain inner-denominator)
RationalCompositionPredicate
  inner-numerator inner-denominator outer-denominator point =
    0＃ₚ
      (outer-denominator
        (divideOnApartDenominatorDomain
          inner-numerator inner-denominator point))

RationalCompositionDomain :
  (inner-numerator inner-denominator outer-denominator : ℝ → ℝ) →
  Type
RationalCompositionDomain
  inner-numerator inner-denominator outer-denominator =
    Σ[ point ∈ ApartDenominatorDomain inner-denominator ]
      point ∈ RationalCompositionPredicate
        inner-numerator inner-denominator outer-denominator

RationalCompositionDomainPremetricSpace :
  (inner-numerator inner-denominator outer-denominator : ℝ → ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
RationalCompositionDomainPremetricSpace
  inner-numerator inner-denominator outer-denominator =
    PremetricSubspace
      (ApartDenominatorDomainPremetricSpace inner-denominator)
      (RationalCompositionPredicate
        inner-numerator inner-denominator outer-denominator)

rationalCompositionDomainCoordinate :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ℝ
rationalCompositionDomainCoordinate
  inner-numerator inner-denominator outer-denominator point =
  fst (fst point)

rationalCompositionDomainCoordinateNE :
  ∀ inner-numerator inner-denominator outer-denominator →
  NE[
    RationalCompositionDomainPremetricSpace
      inner-numerator inner-denominator outer-denominator
    ,
    ℝPremetricSpace
    ]
fst
  (rationalCompositionDomainCoordinateNE
      inner-numerator inner-denominator outer-denominator) =
      rationalCompositionDomainCoordinate
        inner-numerator inner-denominator outer-denominator
IsNonExpanding.pres≈
  (snd
    (rationalCompositionDomainCoordinateNE
      inner-numerator inner-denominator outer-denominator))
  point other ε =
    idfun _

rationalCompositionDomainCoordinateIsContinuous :
  ∀ inner-numerator inner-denominator outer-denominator →
  isContinuous
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (rationalCompositionDomainCoordinate
      inner-numerator inner-denominator outer-denominator)
    (snd ℝPremetricSpace)
rationalCompositionDomainCoordinateIsContinuous
  inner-numerator inner-denominator outer-denominator =
    snd
      (NE→C
        (rationalCompositionDomainCoordinateNE
          inner-numerator inner-denominator outer-denominator))

rationalCompositionDomainInnerPoint :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ApartDenominatorDomain inner-denominator
rationalCompositionDomainInnerPoint
  inner-numerator inner-denominator outer-denominator =
  fst

rationalCompositionDomainInnerPointNE :
  ∀ inner-numerator inner-denominator outer-denominator →
  NE[
    RationalCompositionDomainPremetricSpace
      inner-numerator inner-denominator outer-denominator
    ,
    ApartDenominatorDomainPremetricSpace inner-denominator
    ]
rationalCompositionDomainInnerPointNE
  inner-numerator inner-denominator outer-denominator =
    subspaceInclusionNE
      (ApartDenominatorDomainPremetricSpace inner-denominator)
      (RationalCompositionPredicate
        inner-numerator inner-denominator outer-denominator)

innerRationalFunctionOnCompositionDomain :
  (inner-numerator inner-denominator outer-denominator : ℝ → ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ℝ
innerRationalFunctionOnCompositionDomain
  inner-numerator inner-denominator outer-denominator point =
    divideOnApartDenominatorDomain
      inner-numerator inner-denominator
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator point)

innerRationalFunctionDerivativeOnCompositionDomain :
  (inner-numerator inner-denominator outer-denominator
   inner-numerator-derivative inner-denominator-derivative : ℝ → ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ℝ
innerRationalFunctionDerivativeOnCompositionDomain
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
      inner-numerator inner-denominator
      inner-numerator-derivative inner-denominator-derivative
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator point)

innerRationalFunctionOnCompositionDomainHasDerivativeAlong :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative
    inner-numerator inner-numerator-derivative →
  IsDerivative
    inner-denominator inner-denominator-derivative →
  IsDerivativeAlong
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (rationalCompositionDomainCoordinate
      inner-numerator inner-denominator outer-denominator)
    (innerRationalFunctionOnCompositionDomain
      inner-numerator inner-denominator outer-denominator)
    (innerRationalFunctionDerivativeOnCompositionDomain
      inner-numerator inner-denominator outer-denominator
      inner-numerator-derivative inner-denominator-derivative)
innerRationalFunctionOnCompositionDomainHasDerivativeAlong
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace inner-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        inner-numerator inner-denominator)
      (divideOnApartDenominatorDomainConventionalDerivative
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative)
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator)
      (snd
        (NE→C
          (rationalCompositionDomainInnerPointNE
            inner-numerator inner-denominator outer-denominator)))
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)

innerRationalFunctionOnCompositionDomainIsContinuous :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative
    inner-numerator inner-numerator-derivative →
  IsDerivative
    inner-denominator inner-denominator-derivative →
  isContinuous
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (innerRationalFunctionOnCompositionDomain
      inner-numerator inner-denominator outer-denominator)
    (snd ℝPremetricSpace)
innerRationalFunctionOnCompositionDomainIsContinuous
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative =
    derivativeAlongIsContinuous
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (rationalCompositionDomainCoordinate
        inner-numerator inner-denominator outer-denominator)
      (innerRationalFunctionOnCompositionDomain
        inner-numerator inner-denominator outer-denominator)
      (innerRationalFunctionDerivativeOnCompositionDomain
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative)
      (rationalCompositionDomainCoordinateIsContinuous
        inner-numerator inner-denominator outer-denominator)
      (innerRationalFunctionOnCompositionDomainHasDerivativeAlong
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)

rationalCompositionOuterDomainPoint :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ApartDenominatorDomain outer-denominator
rationalCompositionOuterDomainPoint
  inner-numerator inner-denominator outer-denominator point =
  innerRationalFunctionOnCompositionDomain
      inner-numerator inner-denominator outer-denominator point
  , snd point

rationalCompositionOuterDomainPointIsContinuous :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative
    inner-numerator inner-numerator-derivative →
  IsDerivative
    inner-denominator inner-denominator-derivative →
  isContinuous
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (rationalCompositionOuterDomainPoint
      inner-numerator inner-denominator outer-denominator)
    (snd
      (ApartDenominatorDomainPremetricSpace outer-denominator))
rationalCompositionOuterDomainPointIsContinuous
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative point
  .IsContinuousAt.pres≈ ε =
    innerRationalFunctionOnCompositionDomainIsContinuous
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative
        point
      .IsContinuousAt.pres≈ ε

composeRationalFunctionsOnNaturalDomain :
  (inner-numerator inner-denominator
   outer-numerator outer-denominator : ℝ → ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ℝ
composeRationalFunctionsOnNaturalDomain
  inner-numerator inner-denominator
  outer-numerator outer-denominator point =
    divideOnApartDenominatorDomain
      outer-numerator outer-denominator
      (rationalCompositionOuterDomainPoint
        inner-numerator inner-denominator outer-denominator point)

composeRationalFunctionsDerivativeOnNaturalDomain :
  (inner-numerator inner-denominator
   outer-numerator outer-denominator
   inner-numerator-derivative inner-denominator-derivative
   outer-numerator-derivative outer-denominator-derivative : ℝ → ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
    →
  ℝ
composeRationalFunctionsDerivativeOnNaturalDomain
  inner-numerator inner-denominator
  outer-numerator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-numerator-derivative outer-denominator-derivative point =
    divideOnApartDenominatorDomainConventionalDerivative
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative
        (rationalCompositionOuterDomainPoint
          inner-numerator inner-denominator outer-denominator point)
      · innerRationalFunctionDerivativeOnCompositionDomain
          inner-numerator inner-denominator outer-denominator
          inner-numerator-derivative inner-denominator-derivative
          point

composeRationalFunctionsOnNaturalDomainHasDerivativeAlong :
  ∀ inner-numerator inner-denominator
    outer-numerator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-numerator-derivative outer-denominator-derivative →
  IsDerivative
    inner-numerator inner-numerator-derivative →
  IsDerivative
    inner-denominator inner-denominator-derivative →
  IsDerivative
    outer-numerator outer-numerator-derivative →
  IsDerivative
    outer-denominator outer-denominator-derivative →
  IsDerivativeAlong
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (rationalCompositionDomainCoordinate
      inner-numerator inner-denominator outer-denominator)
    (composeRationalFunctionsOnNaturalDomain
      inner-numerator inner-denominator
      outer-numerator outer-denominator)
    (composeRationalFunctionsDerivativeOnNaturalDomain
      inner-numerator inner-denominator
      outer-numerator outer-denominator
      inner-numerator-derivative inner-denominator-derivative
      outer-numerator-derivative outer-denominator-derivative)
composeRationalFunctionsOnNaturalDomainHasDerivativeAlong
  inner-numerator inner-denominator
  outer-numerator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-numerator-derivative outer-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative
  outer-numerator-has-derivative
  outer-denominator-has-derivative =
    chainHasDerivativeAlongThrough
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace outer-denominator))
      (rationalCompositionDomainCoordinate
        inner-numerator inner-denominator outer-denominator)
      (rationalCompositionOuterDomainPoint
        inner-numerator inner-denominator outer-denominator)
      apartDenominatorDomainCoordinate
      (innerRationalFunctionDerivativeOnCompositionDomain
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative)
      (divideOnApartDenominatorDomain
        outer-numerator outer-denominator)
      (divideOnApartDenominatorDomainConventionalDerivative
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative)
      (rationalCompositionDomainCoordinateIsContinuous
        inner-numerator inner-denominator outer-denominator)
      (rationalCompositionOuterDomainPointIsContinuous
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)
      (innerRationalFunctionOnCompositionDomainHasDerivativeAlong
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)
      (divideOnApartDenominatorDomainHasConventionalDerivativeAlong
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative
        outer-numerator-has-derivative
        outer-denominator-has-derivative)

rationalCompositionDomainPoint :
  ∀ inner-numerator inner-denominator outer-denominator x →
  (inner-apart : 0 ＃ inner-denominator x) →
  0 ＃
    outer-denominator
      (divideℝ
        (inner-numerator x)
        (inner-denominator x)
        inner-apart) →
  RationalCompositionDomain
    inner-numerator inner-denominator outer-denominator
rationalCompositionDomainPoint
  inner-numerator inner-denominator outer-denominator x
  inner-apart outer-apart =
    (x , inner-apart) , outer-apart
