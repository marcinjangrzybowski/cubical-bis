module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Chain
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.SignedReciprocal

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  variable
    ℓ ℓ' : Level

constantApartDenominator :
  ∀ {A : Type ℓ} (constant : ℝ) →
  0 ＃ constant →
  ∀ (_ : A) → 0 ＃ constant
constantApartDenominator constant constant-apart point =
  constant-apart

positiveDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → ℝ) →
  (∀ point → 0 <ℝ denominator point) →
  ∀ point → 0 ＃ denominator point
positiveDenominatorApart denominator denominator-positive point =
  inl (denominator-positive point)

negativeDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → ℝ) →
  (∀ point → denominator point <ℝ 0) →
  ∀ point → 0 ＃ denominator point
negativeDenominatorApart denominator denominator-negative point =
  inr (denominator-negative point)

negatedDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → ℝ) →
  (∀ point → 0 ＃ denominator point) →
  ∀ point → 0 ＃ (- denominator point)
negatedDenominatorApart denominator denominator-apart point =
  inverseNegApart
    (denominator point) (denominator-apart point)

productDenominatorApart :
  ∀ {A : Type ℓ} (left right : A → ℝ) →
  (∀ point → 0 ＃ left point) →
  (∀ point → 0 ＃ right point) →
  ∀ point → 0 ＃ (left point · right point)
productDenominatorApart
  left right left-apart right-apart point =
    apartMul
      (left point) (right point)
      (left-apart point) (right-apart point)

powerDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → ℝ) (n : ℕ) →
  (∀ point → 0 ＃ denominator point) →
  ∀ point → 0 ＃ (denominator point ^ⁿ n)
powerDenominatorApart denominator n denominator-apart point =
  apartPow
    (denominator point) n (denominator-apart point)

differenceDenominatorApart :
  ∀ {A : Type ℓ} (left right : A → ℝ) →
  (∀ point → left point ＃ right point) →
  ∀ point → 0 ＃ (left point - right point)
differenceDenominatorApart left right values-apart point =
  apart→zeroApartDifference
    (left point) (right point) (values-apart point)

-- A differentiable real coordinate into the apart-real subspace is
-- continuous as a subspace-valued map.  The target closeness is definitionally
-- the closeness of its underlying real coordinate.
apartMapOfDerivativeIsContinuous :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → ApartReal)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong
    source coordinate
    (apartRealCoordinate ∘ denominator)
    denominator-derivative →
  isContinuous
    source denominator
    (snd ApartRealPremetricSpace)
apartMapOfDerivativeIsContinuous
  source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative
  point .IsContinuousAt.pres≈ ε =
    derivativeAlongIsContinuous
        source coordinate
        (apartRealCoordinate ∘ denominator)
        denominator-derivative
        coordinate-continuous
        denominator-has-derivative
        point
      .IsContinuousAt.pres≈ ε

reciprocalOfApartMap :
  ∀ {A : Type ℓ} →
  (A → ApartReal) → A → ℝ
reciprocalOfApartMap denominator =
  apartRealReciprocal ∘ denominator

reciprocalOfApartMapDerivative :
  ∀ {A : Type ℓ}
    (denominator : A → ApartReal) →
  (A → ℝ) → A → ℝ
reciprocalOfApartMapDerivative
  denominator denominator-derivative point =
    apartRealReciprocalDerivative (denominator point)
      · denominator-derivative point

reciprocalOfApartMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (denominator : A → ApartReal)
    (denominator-derivative : A → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong
    source coordinate
    (apartRealCoordinate ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (reciprocalOfApartMap denominator)
    (reciprocalOfApartMapDerivative
      denominator denominator-derivative)
reciprocalOfApartMapHasDerivativeAlong
  source coordinate denominator denominator-derivative
  coordinate-continuous denominator-has-derivative =
    chainHasDerivativeAlongThrough
      source
      (snd ApartRealPremetricSpace)
      coordinate denominator apartRealCoordinate
      denominator-derivative
      apartRealReciprocal apartRealReciprocalDerivative
      coordinate-continuous
      (apartMapOfDerivativeIsContinuous
        source coordinate denominator denominator-derivative
        coordinate-continuous denominator-has-derivative)
      denominator-has-derivative
      apartRealReciprocalHasDerivativeAlong

quotientByApartMap :
  ∀ {A : Type ℓ} →
  (A → ℝ) → (A → ApartReal) → A → ℝ
quotientByApartMap numerator denominator point =
  numerator point · reciprocalOfApartMap denominator point

quotientByApartMapDerivative :
  ∀ {A : Type ℓ}
    (numerator : A → ℝ)
    (denominator : A → ApartReal)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
quotientByApartMapDerivative
  numerator denominator
  numerator-derivative denominator-derivative point =
    numerator-derivative point
        · reciprocalOfApartMap denominator point
      + numerator point
        · reciprocalOfApartMapDerivative
            denominator denominator-derivative point

quotientByApartMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ)
    (numerator : A → ℝ)
    (denominator : A → ApartReal)
    (numerator-derivative denominator-derivative : A → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong
    source coordinate numerator numerator-derivative →
  IsDerivativeAlong
    source coordinate
    (apartRealCoordinate ∘ denominator)
    denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (quotientByApartMap numerator denominator)
    (quotientByApartMapDerivative
      numerator denominator
      numerator-derivative denominator-derivative)
quotientByApartMapHasDerivativeAlong
  source coordinate numerator denominator
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
    mulHasDerivativeAlong
      source coordinate
      numerator (reciprocalOfApartMap denominator)
      numerator-derivative
      (reciprocalOfApartMapDerivative
        denominator denominator-derivative)
      coordinate-continuous
      numerator-has-derivative
      (reciprocalOfApartMapHasDerivativeAlong
        source coordinate denominator denominator-derivative
        coordinate-continuous denominator-has-derivative)

apartDenominatorMap :
  ∀ {A : Type ℓ}
    (denominator : A → ℝ) →
  (∀ point → 0 ＃ denominator point) →
  A → ApartReal
apartDenominatorMap denominator denominator-apart point =
  denominator point , denominator-apart point

divideByApartDenominator :
  ∀ {A : Type ℓ}
    (numerator denominator : A → ℝ) →
  (∀ point → 0 ＃ denominator point) →
  A → ℝ
divideByApartDenominator
  numerator denominator denominator-apart point =
    divideℝ
      (numerator point) (denominator point)
      (denominator-apart point)

divideByApartDenominatorDerivative :
  ∀ {A : Type ℓ}
    (numerator denominator : A → ℝ)
    (denominator-apart : ∀ point → 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → ℝ) →
  A → ℝ
divideByApartDenominatorDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative point =
    numerator-derivative point
        · inverseℝ
            (denominator point) (denominator-apart point)
      + numerator point
        ·
          ( - (inverseℝ
                  (denominator point) (denominator-apart point)
                · inverseℝ
                    (denominator point) (denominator-apart point))
            · denominator-derivative point
          )

divideByApartDenominatorHasDerivativeAlong :
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
    (divideByApartDenominatorDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasDerivativeAlong
  source coordinate numerator denominator denominator-apart
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
    quotientByApartMapHasDerivativeAlong
      source coordinate numerator
      (apartDenominatorMap denominator denominator-apart)
      numerator-derivative denominator-derivative
      coordinate-continuous
      numerator-has-derivative denominator-has-derivative

divideByApartDenominatorHasDerivative :
  ∀ (numerator denominator : ℝ → ℝ)
    (denominator-apart : ∀ x → 0 ＃ denominator x)
    (numerator-derivative denominator-derivative : ℝ → ℝ) →
  IsDerivative numerator numerator-derivative →
  IsDerivative denominator denominator-derivative →
  IsDerivative
    (divideByApartDenominator
      numerator denominator denominator-apart)
    (divideByApartDenominatorDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
    divideByApartDenominatorHasDerivativeAlong
      (snd ℝPremetricSpace)
      (idfun ℝ)
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
      (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
