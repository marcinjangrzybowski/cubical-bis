module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.SignedReciprocal


private
  variable
    ℓ ℓ' : Level

  module AbstractQuotient {ℓR} (R : CommRing ℓR) where
    open CommRingStr (snd R)
    open RingTheory (CommRing→Ring R)

    rearrange : ∀ a b c d →
      (a · b) · (c · d) ≡ (a · c) · (b · d)
    rearrange a b c d = solve! R

    moveNegative : ∀ a b c →
      a · ((- b) · c) ≡ - ((a · c) · b)
    moveNegative a b c = solve! R

    quotient : ∀ a b c d i → b · i ≡ 1r →
      (a · i) + (c · ((- (i · i)) · d))
        ≡
      ((a · b) + (- (c · d))) · (i · i)
    quotient a b c d i bi≡1 =
      cong
        (_+ (c · ((- (i · i)) · d)))
        (sym (·IdR (a · i))
        ∙ cong ((a · i) ·_) (sym bi≡1))
      ∙ cong₂ _+_
          (rearrange a i b i)
          (moveNegative c (i · i) d)
      ∙ sym (·DistL- (a · b) (c · d) (i · i))

constantApartDenominator :
  ∀ {A : Type ℓ} (constant : Real.ℝ) →
  Real.ιℚ 0 ＃ constant →
  ∀ (_ : A) → Real.ιℚ 0 ＃ constant
constantApartDenominator constant constant-apart point =
  constant-apart


positiveDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → Real.ℝ) →
  (∀ point → Real.ιℚ 0 <ℝ denominator point) →
  ∀ point → Real.ιℚ 0 ＃ denominator point
positiveDenominatorApart denominator denominator-positive point =
  inl (denominator-positive point)


negativeDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → Real.ℝ) →
  (∀ point → denominator point <ℝ Real.ιℚ 0) →
  ∀ point → Real.ιℚ 0 ＃ denominator point
negativeDenominatorApart denominator denominator-negative point =
  inr (denominator-negative point)


negatedDenominatorApart :
  ∀ {A : Type ℓ} (denominator : A → Real.ℝ) →
  (∀ point → Real.ιℚ 0 ＃ denominator point) →
  ∀ point → Real.ιℚ 0 ＃ Neg.- denominator point
negatedDenominatorApart denominator denominator-apart point =
  inverseNegApart
    (denominator point) (denominator-apart point)


differenceDenominatorApart :
  ∀ {A : Type ℓ} (left right : A → Real.ℝ) →
  (∀ point → left point ＃ right point) →
  ∀ point →
    Real.ιℚ 0 ＃ (left point Group.- right point)
differenceDenominatorApart left right values-apart point =
  apart→zeroApartDifference
    (left point) (right point) (values-apart point)


-- Differentiability of the underlying real coordinate gives continuity of
-- the map into the inherited apart-real premetric.  The proof component of
-- the subspace does not appear in closeness.

apartMapOfDerivativeIsContinuous :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ)
    (denominator : A → ApartReal)
    (denominator-derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
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
  (A → ApartReal) → A → Real.ℝ
reciprocalOfApartMap denominator =
  apartRealReciprocal ∘ denominator


reciprocalOfApartMapDerivative :
  ∀ {A : Type ℓ}
    (denominator : A → ApartReal) →
  (A → Real.ℝ) → A → Real.ℝ
reciprocalOfApartMapDerivative
  denominator denominator-derivative point =
  apartRealReciprocalDerivative (denominator point) Mul.·
    denominator-derivative point


reciprocalOfApartMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ)
    (denominator : A → ApartReal)
    (denominator-derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
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
  chainHasDerivativeAlongIndexed
    source coordinate
    (apartRealCoordinate ∘ denominator)
    denominator-derivative
    (reciprocalOfApartMap denominator)
    (apartRealReciprocalDerivative ∘ denominator)
    denominator-has-derivative
    reciprocal-along-denominator
  where
  denominator-continuous :
    isContinuous source denominator
      (snd ApartRealPremetricSpace)
  denominator-continuous =
    apartMapOfDerivativeIsContinuous
      source coordinate denominator denominator-derivative
      coordinate-continuous denominator-has-derivative

  reciprocal-along-denominator :
    IsDerivativeAlong
      source
      (apartRealCoordinate ∘ denominator)
      (reciprocalOfApartMap denominator)
      (apartRealReciprocalDerivative ∘ denominator)
  reciprocal-along-denominator =
    pullbackHasDerivativeAlong
      source
      (snd ApartRealPremetricSpace)
      apartRealCoordinate
      apartRealReciprocal
      apartRealReciprocalDerivative
      denominator denominator-continuous
      apartRealReciprocalHasDerivativeAlong


quotientByApartMap :
  ∀ {A : Type ℓ} →
  (A → Real.ℝ) → (A → ApartReal) → A → Real.ℝ
quotientByApartMap numerator denominator point =
  numerator point Mul.· reciprocalOfApartMap denominator point


quotientByApartMapDerivative :
  ∀ {A : Type ℓ}
    (numerator : A → Real.ℝ)
    (denominator : A → ApartReal)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  A → Real.ℝ
quotientByApartMapDerivative
  numerator denominator
  numerator-derivative denominator-derivative point =
  (numerator-derivative point Mul.·
      reciprocalOfApartMap denominator point)
  Add.+
  (numerator point Mul.·
    reciprocalOfApartMapDerivative
      denominator denominator-derivative point)


quotientByApartMapHasDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ)
    (numerator : A → Real.ℝ)
    (denominator : A → ApartReal)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
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
    (denominator : A → Real.ℝ) →
  (∀ point → Real.ιℚ 0 ＃ denominator point) →
  A → ApartReal
apartDenominatorMap denominator denominator-apart point =
  denominator point , denominator-apart point


divideByApartDenominator :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ) →
  (∀ point → Real.ιℚ 0 ＃ denominator point) →
  A → Real.ℝ
divideByApartDenominator
  numerator denominator denominator-apart point =
  divideℝ
    (numerator point) (denominator point)
    (denominator-apart point)


divideByApartDenominatorDerivative :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  A → Real.ℝ
divideByApartDenominatorDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative point =
  (numerator-derivative point Mul.·
    inverseℝ (denominator point) (denominator-apart point))
  Add.+
  (numerator point Mul.·
    (Neg.-
      (inverseℝ (denominator point) (denominator-apart point) Mul.·
       inverseℝ (denominator point) (denominator-apart point))
      Mul.· denominator-derivative point))


divideByApartDenominatorHasDerivativeAlong :
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
    (divideByApartDenominatorDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
  divideByApartDenominatorHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)
    numerator denominator denominator-apart
    numerator-derivative denominator-derivative
    (snd (CategoryStructures.idᶜ {M = Real.ℝPremetricSpace}))


-- A normalization-friendly quotient-rule presentation.  Writing the
-- denominator factor as two already-constructed reciprocals avoids forcing
-- Agda to normalize a proof-indexed reciprocal of `g²` while still exposing
-- exactly the algebraic content of `(f′g - fg′) / g²`.

quotientRuleNormalizedDerivative :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  A → Real.ℝ
quotientRuleNormalizedDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative point =
  ((numerator-derivative point Mul.· denominator point) Group.-
    (numerator point Mul.· denominator-derivative point)) Mul.·
  (inverseℝ (denominator point) (denominator-apart point) Mul.·
    inverseℝ (denominator point) (denominator-apart point))


divideByApartDenominatorDerivative≡Normalized :
  ∀ {A : Type ℓ}
    (numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  divideByApartDenominatorDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
    ≡
  quotientRuleNormalizedDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative
divideByApartDenominatorDerivative≡Normalized
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
  funExt λ point →
    AbstractQuotient.quotient
      ℝCommRing
      (numerator-derivative point)
      (denominator point)
      (numerator point)
      (denominator-derivative point)
      (inverseℝ (denominator point) (denominator-apart point))
      (inverseℝLaw (denominator point) (denominator-apart point))


divideByApartDenominatorHasNormalizedDerivativeAlong :
  ∀ {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate numerator denominator : A → Real.ℝ)
    (denominator-apart :
      ∀ point → Real.ιℚ 0 ＃ denominator point)
    (numerator-derivative denominator-derivative : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate numerator numerator-derivative →
  IsDerivativeAlong source coordinate denominator denominator-derivative →
  IsDerivativeAlong
    source coordinate
    (divideByApartDenominator
      numerator denominator denominator-apart)
    (quotientRuleNormalizedDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasNormalizedDerivativeAlong
  source coordinate numerator denominator denominator-apart
  numerator-derivative denominator-derivative
  coordinate-continuous
  numerator-has-derivative denominator-has-derivative =
  subst
    (IsDerivativeAlong
      source coordinate
      (divideByApartDenominator
        numerator denominator denominator-apart))
    (divideByApartDenominatorDerivative≡Normalized
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
    (divideByApartDenominatorHasDerivativeAlong
      source coordinate numerator denominator denominator-apart
      numerator-derivative denominator-derivative
      coordinate-continuous
      numerator-has-derivative denominator-has-derivative)


divideByApartDenominatorHasNormalizedDerivative :
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
    (quotientRuleNormalizedDerivative
      numerator denominator denominator-apart
      numerator-derivative denominator-derivative)
divideByApartDenominatorHasNormalizedDerivative
  numerator denominator denominator-apart
  numerator-derivative denominator-derivative =
  divideByApartDenominatorHasNormalizedDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)
    numerator denominator denominator-apart
    numerator-derivative denominator-derivative
    (snd (CategoryStructures.idᶜ {M = Real.ℝPremetricSpace}))
