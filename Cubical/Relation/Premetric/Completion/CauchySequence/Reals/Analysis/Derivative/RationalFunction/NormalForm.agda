module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Quotient
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain


private
  variable
    ℓ ℓ' : Level


quotientRuleNumerator :
  ∀ {A : Type ℓ} →
  (numerator denominator
   numerator-derivative denominator-derivative : A → Real.ℝ) →
  A → Real.ℝ
quotientRuleNumerator
  numerator denominator
  numerator-derivative denominator-derivative point =
    (numerator-derivative point Mul.· denominator point) Group.-
      (numerator point Mul.· denominator-derivative point)


denominatorSquareApart :
  ∀ {A : Type ℓ}
    (denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point) →
  ∀ point →
  Real.ιℚ 0 ＃
    (denominator point Mul.· denominator point)
denominatorSquareApart denominator denominator-apart point =
  apartMul
    (denominator point) (denominator point)
    (denominator-apart point) (denominator-apart point)


-- The familiar quotient-rule normal form `(f′g - fg′) / g²`.
-- Its squared-denominator inverse is definitionally tied to the canonical
-- apartness proof above; proof irrelevance makes the presentation usable
-- with any other proof of the same domain fact.

divideByApartDenominatorConventionalDerivative :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  A → Real.ℝ
divideByApartDenominatorConventionalDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative point =
    divideℝ
      (quotientRuleNumerator
        numerator denominator
        numerator-derivative denominator-derivative point)
      (denominator point Mul.· denominator point)
      (denominatorSquareApart
        denominator denominator-apart point)


-- The computational derivative already used by the library contains two
-- copies of the inverse of `g`.  Multiplicativity of signed inversion is the
-- only additional algebra needed to identify it with division by `g²`.

quotientRuleNormalizedDerivative≡Conventional :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  quotientRuleNormalizedDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
    ≡
  divideByApartDenominatorConventionalDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
quotientRuleNormalizedDerivative≡Conventional
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
    funExt λ point →
      cong
        (quotientRuleNumerator
          numerator denominator
          numerator-derivative denominator-derivative point Mul.·_)
        (sym
          (inverseℝMul
            (denominator point) (denominator point)
            (denominator-apart point)
            (denominator-apart point)))


divideByApartDenominatorDerivative≡Conventional :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  divideByApartDenominatorDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
    ≡
  divideByApartDenominatorConventionalDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
divideByApartDenominatorDerivative≡Conventional
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
    divideByApartDenominatorDerivative≡Normalized
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
  ∙ quotientRuleNormalizedDerivative≡Conventional
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative


divideByApartDenominatorHasConventionalDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate denominator denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (divideByApartDenominator
      numerator denominator denominator-apart)
    (divideByApartDenominatorConventionalDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasConventionalDerivativeAlong
  source coordinate numerator denominator denominator-apart
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
    subst
      (IsDerivativeAlong
        source coordinate
        (divideByApartDenominator
          numerator denominator denominator-apart))
      (quotientRuleNormalizedDerivative≡Conventional
        numerator denominator denominator-apart
        numerator-derivative denominator-derivative)
      (divideByApartDenominatorHasNormalizedDerivativeAlong
        source coordinate numerator denominator denominator-apart
        numerator-derivative denominator-derivative
        coordinate-continuous
        numerator-has-derivative denominator-has-derivative)


divideByApartDenominatorHasConventionalDerivative :
  ∀ (numerator denominator : Real.ℝ → Real.ℝ)
    (denominator-apart :
      ∀ x → Real.ιℚ 0 ＃ denominator x)
    (numerator-derivative denominator-derivative :
      Real.ℝ → Real.ℝ) →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivative
    (divideByApartDenominator
      numerator denominator denominator-apart)
    (divideByApartDenominatorConventionalDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasConventionalDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
    divideByApartDenominatorHasConventionalDerivativeAlong
      (snd Real.ℝPremetricSpace)
      (idfun Real.ℝ)
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
      (snd (CategoryStructures.idᶜ {M = Real.ℝPremetricSpace}))


divideOnApartDenominatorDomainConventionalDerivative :
  (numerator denominator
   numerator-derivative denominator-derivative :
    Real.ℝ → Real.ℝ) →
  ApartDenominatorDomain denominator → Real.ℝ
divideOnApartDenominatorDomainConventionalDerivative
  numerator denominator
  numerator-derivative denominator-derivative =
    divideByApartDenominatorConventionalDerivative
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      (λ point → snd point)
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)


divideOnApartDenominatorDomainDerivative≡Conventional :
  ∀ numerator denominator
    numerator-derivative denominator-derivative →
  divideOnApartDenominatorDomainDerivative
      numerator denominator
      numerator-derivative denominator-derivative
    ≡
  divideOnApartDenominatorDomainConventionalDerivative
      numerator denominator
      numerator-derivative denominator-derivative
divideOnApartDenominatorDomainDerivative≡Conventional
  numerator denominator
  numerator-derivative denominator-derivative =
    quotientRuleNormalizedDerivative≡Conventional
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      (λ point → snd point)
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)


divideOnApartDenominatorDomainHasConventionalDerivativeAlong :
  ∀ numerator denominator
    numerator-derivative denominator-derivative →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivativeAlong
    (snd (ApartDenominatorDomainPremetricSpace denominator))
    apartDenominatorDomainCoordinate
    (divideOnApartDenominatorDomain numerator denominator)
    (divideOnApartDenominatorDomainConventionalDerivative
      numerator denominator
      numerator-derivative denominator-derivative)
divideOnApartDenominatorDomainHasConventionalDerivativeAlong
  numerator denominator
  numerator-derivative denominator-derivative
  numerator-has-derivative denominator-has-derivative =
    subst
      (IsDerivativeAlong
        (snd (ApartDenominatorDomainPremetricSpace denominator))
        apartDenominatorDomainCoordinate
        (divideOnApartDenominatorDomain numerator denominator))
      (divideOnApartDenominatorDomainDerivative≡Conventional
        numerator denominator
        numerator-derivative denominator-derivative)
      (divideOnApartDenominatorDomainHasDerivativeAlong
        numerator denominator
        numerator-derivative denominator-derivative
        numerator-has-derivative denominator-has-derivative)


divideOnApartDenominatorDomainConventionalDerivative-proofIrrelevant :
  ∀ numerator denominator
    numerator-derivative denominator-derivative x
    (left right : Real.ιℚ 0 ＃ denominator x) →
  divideOnApartDenominatorDomainConventionalDerivative
      numerator denominator
      numerator-derivative denominator-derivative
      (x , left)
    ≡
  divideOnApartDenominatorDomainConventionalDerivative
      numerator denominator
      numerator-derivative denominator-derivative
      (x , right)
divideOnApartDenominatorDomainConventionalDerivative-proofIrrelevant
  numerator denominator
  numerator-derivative denominator-derivative x left right =
    sym
      (funExt⁻
        (divideOnApartDenominatorDomainDerivative≡Conventional
          numerator denominator
          numerator-derivative denominator-derivative)
        (x , left))
  ∙ divideOnApartDenominatorDomainDerivative-proofIrrelevant
      numerator denominator
      numerator-derivative denominator-derivative x left right
  ∙ funExt⁻
      (divideOnApartDenominatorDomainDerivative≡Conventional
        numerator denominator
        numerator-derivative denominator-derivative)
      (x , right)
