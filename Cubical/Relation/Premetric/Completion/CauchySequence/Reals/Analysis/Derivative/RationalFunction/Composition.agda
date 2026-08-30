module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.SignedReciprocal


-- Composition has two dependent constructive domain obligations: the inner
-- denominator is apart at the original coordinate, and the outer
-- denominator is apart at the resulting inner quotient.  The nested
-- subspace records that dependency without selecting either witness.

RationalCompositionPredicate :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  ℙ (ApartDenominatorDomain inner-denominator)
RationalCompositionPredicate
  inner-numerator inner-denominator outer-denominator point =
    0＃ₚ
      (outer-denominator
        (divideOnApartDenominatorDomain
          inner-numerator inner-denominator point))


RationalCompositionDomain :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  Type
RationalCompositionDomain
  inner-numerator inner-denominator outer-denominator =
    Σ[ point ∈ ApartDenominatorDomain inner-denominator ]
      point ∈ RationalCompositionPredicate
        inner-numerator inner-denominator outer-denominator


RationalCompositionDomainPremetricSpace :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
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
      inner-numerator inner-denominator outer-denominator →
  Real.ℝ
rationalCompositionDomainCoordinate
  inner-numerator inner-denominator outer-denominator point =
    fst (fst point)


rationalCompositionDomainCoordinateNE :
  ∀ inner-numerator inner-denominator outer-denominator →
  NE[
    RationalCompositionDomainPremetricSpace
      inner-numerator inner-denominator outer-denominator
    ,
    Real.ℝPremetricSpace
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
    (snd Real.ℝPremetricSpace)
rationalCompositionDomainCoordinateIsContinuous
  inner-numerator inner-denominator outer-denominator =
    snd
      (NE→C
        (rationalCompositionDomainCoordinateNE
          inner-numerator inner-denominator outer-denominator))


rationalCompositionDomainInnerPoint :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
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
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
  Real.ℝ
innerRationalFunctionOnCompositionDomain
  inner-numerator inner-denominator outer-denominator point =
    divideOnApartDenominatorDomain
      inner-numerator inner-denominator
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator point)


innerRationalFunctionDerivativeOnCompositionDomain :
  (inner-numerator inner-denominator outer-denominator
   inner-numerator-derivative inner-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
  Real.ℝ
innerRationalFunctionDerivativeOnCompositionDomain
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative point =
    divideOnApartDenominatorDomainDerivative
      inner-numerator inner-denominator
      inner-numerator-derivative inner-denominator-derivative
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator point)


innerRationalFunctionOnCompositionDomainHasDerivativeAlong :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
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
  inner-numerator-has-derivative inner-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (snd
        (ApartDenominatorDomainPremetricSpace inner-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        inner-numerator inner-denominator)
      (divideOnApartDenominatorDomainDerivative
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative)
      (rationalCompositionDomainInnerPoint
        inner-numerator inner-denominator outer-denominator)
      (snd
        (NE→C
          (rationalCompositionDomainInnerPointNE
            inner-numerator inner-denominator outer-denominator)))
      (divideOnApartDenominatorDomainHasDerivativeAlong
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)


innerRationalFunctionOnCompositionDomainIsContinuous :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  isContinuous
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (innerRationalFunctionOnCompositionDomain
      inner-numerator inner-denominator outer-denominator)
    (snd Real.ℝPremetricSpace)
innerRationalFunctionOnCompositionDomainIsContinuous
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  inner-numerator-has-derivative inner-denominator-has-derivative =
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


-- The dependent outer condition is itself open in the inner denominator
-- domain.  This strengthens the raw nested-domain construction and is later
-- reusable for local extension theorems.

rationalCompositionPredicateIsOpen :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  IsDerivative outer-denominator outer-denominator-derivative →
  IsOpenPredicate
    (snd (ApartDenominatorDomainPremetricSpace inner-denominator))
    (RationalCompositionPredicate
      inner-numerator inner-denominator outer-denominator)
rationalCompositionPredicateIsOpen
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative
  outer-denominator-has-derivative =
    continuousPreimageIsOpen
      (outer-denominator ∘
        divideOnApartDenominatorDomain
          inner-numerator inner-denominator)
      ApartRealPredicate
      outer-after-inner-continuous
      apartRealPredicateIsOpen
  where
  outer-after-inner-has-derivative :
    IsDerivativeAlong
      (snd (ApartDenominatorDomainPremetricSpace inner-denominator))
      apartDenominatorDomainCoordinate
      (outer-denominator ∘
        divideOnApartDenominatorDomain
          inner-numerator inner-denominator)
      (λ point →
        outer-denominator-derivative
            (divideOnApartDenominatorDomain
              inner-numerator inner-denominator point)
          Mul.·
        divideOnApartDenominatorDomainDerivative
          inner-numerator inner-denominator
          inner-numerator-derivative inner-denominator-derivative
          point)
  outer-after-inner-has-derivative =
    chainHasDerivativeAlong
      (snd (ApartDenominatorDomainPremetricSpace inner-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        inner-numerator inner-denominator)
      (divideOnApartDenominatorDomainDerivative
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative)
      outer-denominator outer-denominator-derivative
      (apartDenominatorDomainCoordinateIsContinuous inner-denominator)
      (divideOnApartDenominatorDomainHasDerivativeAlong
        inner-numerator inner-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)
      outer-denominator-has-derivative

  outer-after-inner-continuous :
    isContinuous
      (snd (ApartDenominatorDomainPremetricSpace inner-denominator))
      (outer-denominator ∘
        divideOnApartDenominatorDomain
          inner-numerator inner-denominator)
      (snd Real.ℝPremetricSpace)
  outer-after-inner-continuous =
    derivativeAlongIsContinuous
      (snd (ApartDenominatorDomainPremetricSpace inner-denominator))
      apartDenominatorDomainCoordinate
      (outer-denominator ∘
        divideOnApartDenominatorDomain
          inner-numerator inner-denominator)
      (λ point →
        outer-denominator-derivative
            (divideOnApartDenominatorDomain
              inner-numerator inner-denominator point)
          Mul.·
        divideOnApartDenominatorDomainDerivative
          inner-numerator inner-denominator
          inner-numerator-derivative inner-denominator-derivative
          point)
      (apartDenominatorDomainCoordinateIsContinuous inner-denominator)
      outer-after-inner-has-derivative


rationalCompositionOuterDomainPoint :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
  ApartDenominatorDomain outer-denominator
rationalCompositionOuterDomainPoint
  inner-numerator inner-denominator outer-denominator point =
    innerRationalFunctionOnCompositionDomain
      inner-numerator inner-denominator outer-denominator point
    , snd point


rationalCompositionOuterDomainPointIsContinuous :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  isContinuous
    (snd
      (RationalCompositionDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    (rationalCompositionOuterDomainPoint
      inner-numerator inner-denominator outer-denominator)
    (snd (ApartDenominatorDomainPremetricSpace outer-denominator))
rationalCompositionOuterDomainPointIsContinuous
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  inner-numerator-has-derivative inner-denominator-has-derivative point
  .IsContinuousAt.pres≈ ε =
    innerRationalFunctionOnCompositionDomainIsContinuous
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative point
      .IsContinuousAt.pres≈ ε


composeRationalFunctionsOnNaturalDomain :
  (inner-numerator inner-denominator
   outer-numerator outer-denominator : Real.ℝ → Real.ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
  Real.ℝ
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
   outer-numerator-derivative outer-denominator-derivative :
    Real.ℝ → Real.ℝ) →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator →
  Real.ℝ
composeRationalFunctionsDerivativeOnNaturalDomain
  inner-numerator inner-denominator
  outer-numerator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-numerator-derivative outer-denominator-derivative point =
    divideOnApartDenominatorDomainDerivative
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative
        (rationalCompositionOuterDomainPoint
          inner-numerator inner-denominator outer-denominator point)
    Mul.·
    innerRationalFunctionDerivativeOnCompositionDomain
      inner-numerator inner-denominator outer-denominator
      inner-numerator-derivative inner-denominator-derivative point


composeRationalFunctionsOnNaturalDomainHasDerivativeAlong :
  ∀ inner-numerator inner-denominator
    outer-numerator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-numerator-derivative outer-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  IsDerivative outer-numerator outer-numerator-derivative →
  IsDerivative outer-denominator outer-denominator-derivative →
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
  inner-numerator-has-derivative inner-denominator-has-derivative
  outer-numerator-has-derivative outer-denominator-has-derivative =
    chainHasDerivativeAlongIndexed
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
      (composeRationalFunctionsOnNaturalDomain
        inner-numerator inner-denominator
        outer-numerator outer-denominator)
      (λ point →
        divideOnApartDenominatorDomainDerivative
          outer-numerator outer-denominator
          outer-numerator-derivative outer-denominator-derivative
          (rationalCompositionOuterDomainPoint
            inner-numerator inner-denominator outer-denominator point))
      (innerRationalFunctionOnCompositionDomainHasDerivativeAlong
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)
      outer-has-derivative-along-inner
  where
  outer-has-derivative-along-inner :
    IsDerivativeAlong
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (innerRationalFunctionOnCompositionDomain
        inner-numerator inner-denominator outer-denominator)
      (composeRationalFunctionsOnNaturalDomain
        inner-numerator inner-denominator
        outer-numerator outer-denominator)
      (λ point →
        divideOnApartDenominatorDomainDerivative
          outer-numerator outer-denominator
          outer-numerator-derivative outer-denominator-derivative
          (rationalCompositionOuterDomainPoint
            inner-numerator inner-denominator outer-denominator point))
  outer-has-derivative-along-inner =
    pullbackHasDerivativeAlong
      (snd
        (RationalCompositionDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
      (snd (ApartDenominatorDomainPremetricSpace outer-denominator))
      apartDenominatorDomainCoordinate
      (divideOnApartDenominatorDomain
        outer-numerator outer-denominator)
      (divideOnApartDenominatorDomainDerivative
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative)
      (rationalCompositionOuterDomainPoint
        inner-numerator inner-denominator outer-denominator)
      (rationalCompositionOuterDomainPointIsContinuous
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative)
      (divideOnApartDenominatorDomainHasDerivativeAlong
        outer-numerator outer-denominator
        outer-numerator-derivative outer-denominator-derivative
        outer-numerator-has-derivative
        outer-denominator-has-derivative)


rationalCompositionDomainPoint :
  ∀ inner-numerator inner-denominator outer-denominator x →
  (inner-apart : Real.ιℚ 0 ＃ inner-denominator x) →
  Real.ιℚ 0 ＃
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


-- The nested representation above is ideal for composing partial maps.  For
-- local-to-ambient reasoning it is useful to reassociate the same evidence
-- into a single proposition on the base real.  The dependent Sigma remains
-- a proposition because both apartness witnesses are propositions and the
-- inner quotient is proof-irrelevant.

RationalCompositionAmbientPredicate :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  ℙ Real.ℝ
RationalCompositionAmbientPredicate
  inner-numerator inner-denominator outer-denominator x =
    ( Σ[ inner-apart ∈ Real.ιℚ 0 ＃ inner-denominator x ]
        Real.ιℚ 0 ＃
          outer-denominator
            (divideℝ
              (inner-numerator x)
              (inner-denominator x)
              inner-apart)
    )
    , isPropΣ
        (isProp＃ (Real.ιℚ 0) (inner-denominator x))
        (λ inner-apart →
          isProp＃ (Real.ιℚ 0)
            (outer-denominator
              (divideℝ
                (inner-numerator x)
                (inner-denominator x)
                inner-apart)))


RationalCompositionAmbientDomain :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  Type
RationalCompositionAmbientDomain
  inner-numerator inner-denominator outer-denominator =
    Σ[ x ∈ Real.ℝ ]
      x ∈ RationalCompositionAmbientPredicate
        inner-numerator inner-denominator outer-denominator


RationalCompositionAmbientDomainPremetricSpace :
  (inner-numerator inner-denominator outer-denominator :
    Real.ℝ → Real.ℝ) →
  PremetricSpace ℓ-zero ℓ-zero
RationalCompositionAmbientDomainPremetricSpace
  inner-numerator inner-denominator outer-denominator =
    PremetricSubspace
      Real.ℝPremetricSpace
      (RationalCompositionAmbientPredicate
        inner-numerator inner-denominator outer-denominator)


rationalCompositionAmbientToNested :
  ∀ inner-numerator inner-denominator outer-denominator →
  RationalCompositionAmbientDomain
      inner-numerator inner-denominator outer-denominator →
  RationalCompositionDomain
      inner-numerator inner-denominator outer-denominator
rationalCompositionAmbientToNested
  inner-numerator inner-denominator outer-denominator
  (x , inner-apart , outer-apart) =
    (x , inner-apart) , outer-apart


rationalCompositionAmbientToNestedNE :
  ∀ inner-numerator inner-denominator outer-denominator →
  NE[
    RationalCompositionAmbientDomainPremetricSpace
      inner-numerator inner-denominator outer-denominator
    ,
    RationalCompositionDomainPremetricSpace
      inner-numerator inner-denominator outer-denominator
  ]
fst
  (rationalCompositionAmbientToNestedNE
    inner-numerator inner-denominator outer-denominator) =
      rationalCompositionAmbientToNested
        inner-numerator inner-denominator outer-denominator
IsNonExpanding.pres≈
  (snd
    (rationalCompositionAmbientToNestedNE
      inner-numerator inner-denominator outer-denominator))
  point other ε =
    idfun _


rationalCompositionAmbientPredicateIsOpen :
  ∀ inner-numerator inner-denominator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  IsDerivative outer-denominator outer-denominator-derivative →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (RationalCompositionAmbientPredicate
      inner-numerator inner-denominator outer-denominator)
rationalCompositionAmbientPredicateIsOpen
  inner-numerator inner-denominator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-denominator-derivative
  inner-numerator-has-derivative
  inner-denominator-has-derivative
  outer-denominator-has-derivative
  x (inner-apart , outer-apart) = do
    (inner-radius , inner-near) ←
      apartDenominatorPredicateOfDerivativeIsOpen
        inner-denominator inner-denominator-derivative
        inner-denominator-has-derivative
        x inner-apart
    (outer-radius , outer-near) ←
      rationalCompositionPredicateIsOpen
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        outer-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative
        outer-denominator-has-derivative
        (x , inner-apart) outer-apart
    return
      ( min₊ inner-radius outer-radius
      , λ y x≈y →
          let
            x≈inner-y :
              x Real.Base.≈ᶜ[ inner-radius ] y
            x≈inner-y =
              PremetricStr.isMonotone≈≤
                (snd Real.ℝPremetricSpace)
                x y (min₊ inner-radius outer-radius) inner-radius
                (min₊≤L inner-radius outer-radius) x≈y

            y-inner-apart :
              Real.ιℚ 0 ＃ inner-denominator y
            y-inner-apart = inner-near y x≈inner-y

            x≈outer-y :
              PremetricStr._≈[_]_
                (snd
                  (ApartDenominatorDomainPremetricSpace
                    inner-denominator))
                (x , inner-apart) outer-radius (y , y-inner-apart)
            x≈outer-y =
              PremetricStr.isMonotone≈≤
                (snd Real.ℝPremetricSpace)
                x y (min₊ inner-radius outer-radius) outer-radius
                (min₊≤R inner-radius outer-radius) x≈y
          in
          y-inner-apart
          , outer-near (y , y-inner-apart) x≈outer-y
      )


composeRationalFunctionsOnAmbientDomainHasDerivativeAlong :
  ∀ inner-numerator inner-denominator
    outer-numerator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-numerator-derivative outer-denominator-derivative →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  IsDerivative outer-numerator outer-numerator-derivative →
  IsDerivative outer-denominator outer-denominator-derivative →
  IsDerivativeAlong
    (snd
      (RationalCompositionAmbientDomainPremetricSpace
        inner-numerator inner-denominator outer-denominator))
    fst
    (composeRationalFunctionsOnNaturalDomain
      inner-numerator inner-denominator
      outer-numerator outer-denominator
      ∘ rationalCompositionAmbientToNested
          inner-numerator inner-denominator outer-denominator)
    (composeRationalFunctionsDerivativeOnNaturalDomain
      inner-numerator inner-denominator
      outer-numerator outer-denominator
      inner-numerator-derivative inner-denominator-derivative
      outer-numerator-derivative outer-denominator-derivative
      ∘ rationalCompositionAmbientToNested
          inner-numerator inner-denominator outer-denominator)
composeRationalFunctionsOnAmbientDomainHasDerivativeAlong
  inner-numerator inner-denominator
  outer-numerator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-numerator-derivative outer-denominator-derivative
  inner-numerator-has-derivative inner-denominator-has-derivative
  outer-numerator-has-derivative outer-denominator-has-derivative =
    pullbackHasDerivativeAlong
      (snd
        (RationalCompositionAmbientDomainPremetricSpace
          inner-numerator inner-denominator outer-denominator))
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
      (rationalCompositionAmbientToNested
        inner-numerator inner-denominator outer-denominator)
      (snd
        (NE→C
          (rationalCompositionAmbientToNestedNE
            inner-numerator inner-denominator outer-denominator)))
      (composeRationalFunctionsOnNaturalDomainHasDerivativeAlong
        inner-numerator inner-denominator
        outer-numerator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        outer-numerator-derivative outer-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative
        outer-numerator-has-derivative
        outer-denominator-has-derivative)


composeRationalFunctionsOnNaturalDomainDerivativeAtWithExtension :
  ∀ inner-numerator inner-denominator
    outer-numerator outer-denominator
    inner-numerator-derivative inner-denominator-derivative
    outer-numerator-derivative outer-denominator-derivative
    extension →
  IsDerivative inner-numerator inner-numerator-derivative →
  IsDerivative inner-denominator inner-denominator-derivative →
  IsDerivative outer-numerator outer-numerator-derivative →
  IsDerivative outer-denominator outer-denominator-derivative →
  (∀ point →
    extension (fst (fst point)) ≡
      composeRationalFunctionsOnNaturalDomain
        inner-numerator inner-denominator
        outer-numerator outer-denominator point) →
  ∀ x →
  (inner-apart : Real.ιℚ 0 ＃ inner-denominator x) →
  (outer-apart :
    Real.ιℚ 0 ＃
      outer-denominator
        (divideℝ
          (inner-numerator x)
          (inner-denominator x)
          inner-apart)) →
  IsDerivativeAt
    extension
    (composeRationalFunctionsDerivativeOnNaturalDomain
      inner-numerator inner-denominator
      outer-numerator outer-denominator
      inner-numerator-derivative inner-denominator-derivative
      outer-numerator-derivative outer-denominator-derivative
      ((x , inner-apart) , outer-apart))
    x
composeRationalFunctionsOnNaturalDomainDerivativeAtWithExtension
  inner-numerator inner-denominator
  outer-numerator outer-denominator
  inner-numerator-derivative inner-denominator-derivative
  outer-numerator-derivative outer-denominator-derivative extension
  inner-numerator-has-derivative inner-denominator-has-derivative
  outer-numerator-has-derivative outer-denominator-has-derivative
  agrees x inner-apart outer-apart =
    openSubspaceDerivativeAtWithExtension
      (RationalCompositionAmbientPredicate
        inner-numerator inner-denominator outer-denominator)
      (rationalCompositionAmbientPredicateIsOpen
        inner-numerator inner-denominator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        outer-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative
        outer-denominator-has-derivative)
      (composeRationalFunctionsOnNaturalDomain
        inner-numerator inner-denominator
        outer-numerator outer-denominator
        ∘ rationalCompositionAmbientToNested
            inner-numerator inner-denominator outer-denominator)
      (composeRationalFunctionsDerivativeOnNaturalDomain
        inner-numerator inner-denominator
        outer-numerator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        outer-numerator-derivative outer-denominator-derivative
        ∘ rationalCompositionAmbientToNested
            inner-numerator inner-denominator outer-denominator)
      extension
      (composeRationalFunctionsOnAmbientDomainHasDerivativeAlong
        inner-numerator inner-denominator
        outer-numerator outer-denominator
        inner-numerator-derivative inner-denominator-derivative
        outer-numerator-derivative outer-denominator-derivative
        inner-numerator-has-derivative
        inner-denominator-has-derivative
        outer-numerator-has-derivative
        outer-denominator-has-derivative)
      (λ point →
        agrees
          (rationalCompositionAmbientToNested
            inner-numerator inner-denominator outer-denominator point))
      x (inner-apart , outer-apart)
