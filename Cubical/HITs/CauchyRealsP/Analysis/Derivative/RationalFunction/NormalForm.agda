module Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Quotient
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.RationalFunction.Domain

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  variable
    ℓ ℓ' : Level

  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  rearrangeFourFactors :
    ∀ (a b c d : ℝ) →
    (a · b) · (c · d) ≡
    (a · c) · (b · d)
  rearrangeFourFactors a b c d =
    mulAssoc a b (c · d)
    ∙ cong (a ·_)
        (sym (mulAssoc b c d))
    ∙ cong (λ value → a · (value · d))
        (mulComm b c)
    ∙ cong (a ·_)
        (mulAssoc c b d)
    ∙ sym (mulAssoc a c (b · d))

  moveNegativeProduct :
    ∀ (a b c : ℝ) →
    a · ((- b) · c) ≡
    - ((a · c) · b)
  moveNegativeProduct a b c =
    cong (a ·_)
      (ℝRing.-DistL· b c)
    ∙ ℝRing.-DistR· a (b · c)
    ∙ cong (-_)
        (cong (a ·_)
          (mulComm b c)
        ∙ sym (mulAssoc a c b))

  -- The inverse law is inserted as a named path first.  The remaining
  -- normalization is an explicit ring calculation, so checking never asks
  -- a solver to inspect completion-valued operations.
  quotientDerivativeAlgebra :
    ∀ (numerator' denominator numerator denominator' inverse : ℝ) →
    denominator · inverse ≡ 1 →
    numerator' · inverse
        + numerator · (- (inverse · inverse) · denominator')
      ≡
    (numerator' · denominator - numerator · denominator')
        · (inverse · inverse)
  quotientDerivativeAlgebra
    numerator' denominator numerator denominator' inverse
    denominator-inverse =
      cong
        (_+ numerator ·
          (- (inverse · inverse) · denominator'))
        (sym (mulIdR (numerator' · inverse)))
      ∙ cong
        (λ unit →
          (numerator' · inverse) · unit
            + numerator ·
                (- (inverse · inverse) · denominator'))
        (sym denominator-inverse)
      ∙ cong₂ _+_
          (rearrangeFourFactors
            numerator' inverse denominator inverse)
          (moveNegativeProduct
            numerator (inverse · inverse) denominator')
      ∙ sym
          (ℝRing.·DistL-
            (numerator' · denominator)
            (numerator · denominator')
            (inverse · inverse))

quotientRuleNumerator :
  ∀ {A : Type ℓ} →
  (numerator denominator
   numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
quotientRuleNumerator
  numerator denominator
  numerator-derivative denominator-derivative point =
    numerator-derivative point · denominator point
      - numerator point · denominator-derivative point

denominatorSquareApart :
  ∀ {A : Type ℓ}
    (denominator : A → ℝ)
    (denominator-apart : ∀ point → 0 ＃ denominator point) →
  ∀ point →
  0 ＃ (denominator point · denominator point)
denominatorSquareApart denominator denominator-apart point =
  apartMul
    (denominator point) (denominator point)
    (denominator-apart point) (denominator-apart point)

-- The conventional quotient-rule presentation `(f'g - fg') / g²`.
divideByApartDenominatorConventionalDerivative :
  ∀ {A : Type ℓ}
    (numerator denominator : A → ℝ)
    (denominator-apart : ∀ point → 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
divideByApartDenominatorConventionalDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative point =
    divideℝ
      (quotientRuleNumerator
        numerator denominator
        numerator-derivative denominator-derivative point)
      (denominator point · denominator point)
      (denominatorSquareApart
        denominator denominator-apart point)

divideByApartDenominatorDerivative≡Conventional :
  ∀ {A : Type ℓ}
    (numerator denominator : A → ℝ)
    (denominator-apart : ∀ point → 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
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
    funExt λ point →
      quotientDerivativeAlgebra
        (numerator-derivative point)
        (denominator point)
        (numerator point)
        (denominator-derivative point)
        (inverseℝ
          (denominator point) (denominator-apart point))
        (inverseℝLaw
          (denominator point) (denominator-apart point))
      ∙ cong
          (quotientRuleNumerator
            numerator denominator
            numerator-derivative denominator-derivative point ·_)
          (sym
            (inverseℝMul
              (denominator point) (denominator point)
              (denominator-apart point)
              (denominator-apart point)))

divideByApartDenominatorHasConventionalDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate numerator denominator : A → ℝ)
    (denominator-apart : ∀ point → 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
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
      (divideByApartDenominatorDerivative≡Conventional
        numerator denominator denominator-apart
        numerator-derivative denominator-derivative)
      (divideByApartDenominatorHasDerivativeAlong
        source coordinate numerator denominator denominator-apart
        numerator-derivative denominator-derivative
        coordinate-continuous
        numerator-has-derivative denominator-has-derivative)

divideByApartDenominatorHasConventionalDerivative :
  ∀ (numerator denominator : ℝ → ℝ)
    (denominator-apart : ∀ x → 0 ＃ denominator x)
    (numerator-derivative denominator-derivative : ℝ → ℝ) →
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
      (snd ℝPremetricSpace)
      (idfun ℝ)
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
      (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))

divideOnApartDenominatorDomainConventionalDerivative :
  (numerator denominator
   numerator-derivative denominator-derivative : ℝ → ℝ) →
  ApartDenominatorDomain denominator → ℝ
divideOnApartDenominatorDomainConventionalDerivative
  numerator denominator
  numerator-derivative denominator-derivative =
    divideByApartDenominatorConventionalDerivative
      (restrictToApartDenominatorDomain numerator)
      (restrictToApartDenominatorDomain denominator)
      central-proof
      (restrictToApartDenominatorDomain numerator-derivative)
      (restrictToApartDenominatorDomain denominator-derivative)
  where
  central-proof :
    ∀ point →
    0 ＃ restrictToApartDenominatorDomain denominator point
  central-proof point = snd point

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
    divideByApartDenominatorHasConventionalDerivativeAlong
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
