module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List
  using (List ; [] ; _∷_)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Chain
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Uniqueness

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

-- The derivative evaluator follows the Horner recurrence directly:
-- D(a + x p(x)) = p(x) + x Dp(x).
evaluatePolynomialDerivative :
  List ℝ → ℝ → ℝ
evaluatePolynomialDerivative [] x =
  0
evaluatePolynomialDerivative
  (a ∷ coefficients) x =
    evaluatePolynomial coefficients x
      + x · evaluatePolynomialDerivative
          coefficients x

-- Weight a coefficient list by consecutive natural numbers.  Starting at
-- one and dropping the constant coefficient gives the usual formal
-- derivative list.
weightPolynomialCoefficients :
  ℕ → List ℝ → List ℝ
weightPolynomialCoefficients n [] =
  []
weightPolynomialCoefficients n
  (coefficient ∷ coefficients) =
    realNatural n · coefficient
      ∷ weightPolynomialCoefficients
          (suc n) coefficients

polynomialDerivativeCoefficients :
  List ℝ → List ℝ
polynomialDerivativeCoefficients [] =
  []
polynomialDerivativeCoefficients
  (constant ∷ coefficients) =
    weightPolynomialCoefficients
      (suc zero) coefficients

private
  commuteWeightedProduct :
    ∀ (a b c : ℝ) →
    a · (b · c) ≡ b · (a · c)
  commuteWeightedProduct a b c =
    sym (mulAssoc a b c)
    ∙ cong (_· c) (mulComm a b)
    ∙ mulAssoc b a c

  weightedPolynomialStep :
    ∀ (n coefficient x tail derivative-tail : ℝ) →
    n · coefficient
        + x · ((n + 1) · tail
          + x · derivative-tail)
      ≡
    n · (coefficient + x · tail)
      + x · (tail + x · derivative-tail)
  weightedPolynomialStep
    n coefficient x tail derivative-tail =
      cong
        (n · coefficient +_)
        (cong
          (x ·_)
          (cong
            (_+ x · derivative-tail)
            (mulDistL n 1 tail
            ∙ cong (n · tail +_)
                (mulIdL tail))))
    ∙ cong
        (n · coefficient +_)
        (mulDistR
          x (n · tail + tail)
          (x · derivative-tail))
    ∙ cong
        (n · coefficient +_)
        (cong
          (_+ x · (x · derivative-tail))
          (mulDistR x (n · tail) tail))
    ∙ addAssoc
        (n · coefficient)
        (x · (n · tail) + x · tail)
        (x · (x · derivative-tail))
    ∙ cong
        (_+ x · (x · derivative-tail))
        (addAssoc
          (n · coefficient)
          (x · (n · tail))
          (x · tail))
    ∙ cong
        (λ value →
          ((n · coefficient + value)
            + x · tail)
            + x · (x · derivative-tail))
        (commuteWeightedProduct x n tail)
    ∙ sym
        (addAssoc
          (n · coefficient + n · (x · tail))
          (x · tail)
          (x · (x · derivative-tail)))
    ∙ cong₂ _+_
        (sym
          (mulDistR
            n coefficient (x · tail)))
        (sym
          (mulDistR
            x tail (x · derivative-tail)))

weightPolynomialEvaluation :
  ∀ n coefficients x →
  evaluatePolynomial
      (weightPolynomialCoefficients n coefficients)
      x
    ≡
  realNatural n
      · evaluatePolynomial coefficients x
    + x · evaluatePolynomialDerivative
        coefficients x
weightPolynomialEvaluation n [] x =
  sym
    (cong₂ _+_
      (mulZeroR (realNatural n))
      (mulZeroR x)
    ∙ addIdL 0)
weightPolynomialEvaluation
  n (coefficient ∷ coefficients) x =
    cong
      (λ value →
        realNatural n · coefficient
          + x · value)
      (weightPolynomialEvaluation
        (suc n) coefficients x)
  ∙ weightedPolynomialStep
      (realNatural n)
      coefficient x
      (evaluatePolynomial coefficients x)
      (evaluatePolynomialDerivative coefficients x)

evaluatePolynomialDerivativeCoefficients :
  ∀ coefficients x →
  evaluatePolynomial
      (polynomialDerivativeCoefficients coefficients)
      x
    ≡
  evaluatePolynomialDerivative coefficients x
evaluatePolynomialDerivativeCoefficients [] x =
  refl
evaluatePolynomialDerivativeCoefficients
  (constant ∷ coefficients) x =
    weightPolynomialEvaluation
      (suc zero) coefficients x
    ∙ cong
        (_+ x · evaluatePolynomialDerivative
          coefficients x)
        (cong
          (_· evaluatePolynomial coefficients x)
          (addIdL 1)
        ∙ mulIdL
            (evaluatePolynomial coefficients x))

-- A division-free two-point polynomial.  Its value on the diagonal is the
-- derivative evaluator above.
evaluatePolynomialDifferenceFactor :
  List ℝ → ℝ → ℝ → ℝ
evaluatePolynomialDifferenceFactor [] x y =
  0
evaluatePolynomialDifferenceFactor
  (a ∷ coefficients) x y =
    evaluatePolynomial coefficients y
      + x · evaluatePolynomialDifferenceFactor
          coefficients x y

private
  hornerForwardDifferencePath :
    ∀ (a x y p q : ℝ) →
    (a + y · p) - (a + x · q)
      ≡
    (y - x) · p + x · (p - q)
  hornerForwardDifferencePath a x y p q =
    sym
      (ℝRing.translatedDifference
        a (y · p) (x · q))
    ∙ product-difference
    where
    yp : ℝ
    yp = y · p

    xp : ℝ
    xp = x · p

    xq : ℝ
    xq = x · q

    product-difference :
      yp - xq
        ≡
      (y - x) · p + x · (p - q)
    product-difference =
      cong (yp +_)
        (sym (addIdL (- xq)))
      ∙ cong (λ value → yp + (value + (- xq)))
          (sym (addInvL xp))
      ∙ addAssoc yp ((- xp) + xp) (- xq)
      ∙ cong (_+ (- xq))
          (addAssoc yp (- xp) xp)
      ∙ sym
          (addAssoc
            (yp + (- xp)) xp (- xq))
      ∙ cong₂ _+_
          (sym (ℝRing.·DistL- y x p))
          (sym (ℝRing.·DistR- x p q))

  commuteNestedProduct :
    ∀ (a b c : ℝ) →
    a · (b · c) ≡ b · (a · c)
  commuteNestedProduct a b c =
    sym (mulAssoc a b c)
    ∙ cong (_· c) (mulComm a b)
    ∙ mulAssoc b a c

evaluatePolynomialDifferenceFactorization :
  ∀ coefficients x y →
  evaluatePolynomial coefficients y
      - evaluatePolynomial coefficients x
    ≡
  (y - x)
    · evaluatePolynomialDifferenceFactor
        coefficients x y
evaluatePolynomialDifferenceFactorization
  [] x y =
    subSelf 0
    ∙ sym (mulZeroR (y - x))
evaluatePolynomialDifferenceFactorization
  (a ∷ coefficients) x y =
    hornerForwardDifferencePath
      a x y tail-y tail-x
    ∙ cong
        ((y - x) · tail-y +_)
        (cong (x ·_)
          (evaluatePolynomialDifferenceFactorization
            coefficients x y))
    ∙ cong
        ((y - x) · tail-y +_)
        (commuteNestedProduct
          x (y - x) factor)
    ∙ sym
        (mulDistR
          (y - x) tail-y (x · factor))
  where
  tail-x : ℝ
  tail-x =
    evaluatePolynomial coefficients x

  tail-y : ℝ
  tail-y =
    evaluatePolynomial coefficients y

  factor : ℝ
  factor =
    evaluatePolynomialDifferenceFactor
      coefficients x y

evaluatePolynomialDifferenceFactorDiagonal :
  ∀ coefficients x →
  evaluatePolynomialDifferenceFactor
      coefficients x x
    ≡
  evaluatePolynomialDerivative coefficients x
evaluatePolynomialDifferenceFactorDiagonal
  [] x =
    refl
evaluatePolynomialDifferenceFactorDiagonal
  (a ∷ coefficients) x =
    cong
      (λ value →
        evaluatePolynomial coefficients x
          + x · value)
      (evaluatePolynomialDifferenceFactorDiagonal
        coefficients x)

evaluatePolynomialDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x y : A → ℝ) →
  isContinuous source x
    (snd ℝPremetricSpace) →
  isContinuous source y
    (snd ℝPremetricSpace) →
  ∀ coefficients →
  isContinuous source
    (λ point →
      evaluatePolynomialDifferenceFactor
        coefficients (x point) (y point))
    (snd ℝPremetricSpace)
evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous
  [] point .IsContinuousAt.pres≈ ε =
    return
      ( 1
      , λ _ _ → refl∼ 0 ε
      )
evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous
  (a ∷ coefficients) =
    addOfContinuousIsContinuous
      source
      (λ point →
        evaluatePolynomial coefficients (y point))
      (λ point →
        x point
          · evaluatePolynomialDifferenceFactor
              coefficients
              (x point) (y point))
      (evaluatePolynomialOfContinuousIsContinuous
        source y y-continuous coefficients)
      (mulOfContinuousIsContinuous
        source x
        (λ point →
          evaluatePolynomialDifferenceFactor
            coefficients
            (x point) (y point))
        x-continuous
        (evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
          source x y
          x-continuous y-continuous
          coefficients))

private
  realPairPremetricSpace :
    PremetricSpace ℓ-zero ℓ-zero
  realPairPremetricSpace =
    PremetricProduct
      ℝPremetricSpace ℝPremetricSpace

  pairLeftIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      fst
      (snd ℝPremetricSpace)
  pairLeftIsContinuous =
    snd
      (productFstC
        {M = ℝPremetricSpace}
        {N = ℝPremetricSpace})

  pairRightIsContinuous :
    isContinuous
      (snd realPairPremetricSpace)
      snd
      (snd ℝPremetricSpace)
  pairRightIsContinuous =
    snd
      (productSndC
        {M = ℝPremetricSpace}
        {N = ℝPremetricSpace})

evaluatePolynomialDifferenceFactorIsContinuous :
  ∀ coefficients →
  isContinuous
    (snd realPairPremetricSpace)
    (λ point →
      evaluatePolynomialDifferenceFactor
        coefficients (fst point) (snd point))
    (snd ℝPremetricSpace)
evaluatePolynomialDifferenceFactorIsContinuous
  coefficients =
    evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
      (snd realPairPremetricSpace)
      fst snd
      pairLeftIsContinuous
      pairRightIsContinuous
      coefficients

evaluatePolynomialOfContinuousHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point →
      evaluatePolynomial
        coefficients (coordinate point))
    (λ point →
      evaluatePolynomialDerivative
        coefficients (coordinate point))
evaluatePolynomialOfContinuousHasDerivativeAlong
  {ℓ = ℓ} {ℓ' = ℓ'} {A = A}
  source coordinate
  coordinate-continuous coefficients =
    continuousDifferenceFactorGivesDerivative
      source coordinate
      (λ point →
        evaluatePolynomial
          coefficients (coordinate point))
      (λ point →
        evaluatePolynomialDerivative
          coefficients (coordinate point))
      (λ points →
        evaluatePolynomialDifferenceFactor
          coefficients
          (coordinate (fst points))
          (coordinate (snd points)))
      (λ x y →
        evaluatePolynomialDifferenceFactorization
          coefficients
          (coordinate x) (coordinate y))
      (λ x →
        evaluatePolynomialDifferenceFactorDiagonal
          coefficients (coordinate x))
      (evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
        (PremetricProductStr source source)
        (coordinate ∘ fst)
        (coordinate ∘ snd)
        (snd left-coordinate)
        (snd right-coordinate)
        coefficients)
  where
  source-space : PremetricSpace ℓ ℓ'
  source-space =
    A , source

  open CategoryStructures

  left-coordinate :
    C[
      PremetricProduct source-space source-space
      , ℝPremetricSpace
    ]
  left-coordinate =
    (coordinate , coordinate-continuous)
      ∘C productFstC

  right-coordinate :
    C[
      PremetricProduct source-space source-space
      , ℝPremetricSpace
    ]
  right-coordinate =
    (coordinate , coordinate-continuous)
      ∘C productSndC

evaluatePolynomialHasDerivative :
  ∀ coefficients →
  IsDerivativeAlong
    (snd ℝPremetricSpace)
    (idfun ℝ)
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients)
evaluatePolynomialHasDerivative coefficients =
  evaluatePolynomialOfContinuousHasDerivativeAlong
    (snd ℝPremetricSpace)
    (idfun ℝ)
    (snd
      (CategoryStructures.idᶜ
        {M = ℝPremetricSpace}))
    coefficients

evaluatePolynomialCompositionHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' : A → ℝ) →
  isContinuous
    source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate inner inner' →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point →
      evaluatePolynomial coefficients (inner point))
    (λ point →
      evaluatePolynomialDerivative
          coefficients (inner point)
        · inner' point)
evaluatePolynomialCompositionHasDerivativeAlong
  source coordinate inner inner'
  coordinate-continuous inner-derivative coefficients =
    chainHasDerivativeAlong
      source coordinate inner inner'
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients)
      coordinate-continuous
      inner-derivative
      (evaluatePolynomialHasDerivative coefficients)

evaluatePolynomialCompositionHasDerivative :
  ∀ inner inner' coefficients →
  IsDerivative inner inner' →
  IsDerivative
    (λ x → evaluatePolynomial coefficients (inner x))
    (λ x →
      evaluatePolynomialDerivative coefficients (inner x)
        · inner' x)
evaluatePolynomialCompositionHasDerivative
  inner inner' coefficients inner-derivative =
    chainHasDerivative
      inner inner'
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients)
      inner-derivative
      (evaluatePolynomialHasDerivative coefficients)

evaluatePolynomialDerivativeUnique :
  ∀ coefficients derivative →
  IsDerivative
    (evaluatePolynomial coefficients)
    derivative →
  derivative ≡ evaluatePolynomialDerivative coefficients
evaluatePolynomialDerivativeUnique
  coefficients derivative has-derivative =
    derivativeFunctionUnique
      (evaluatePolynomial coefficients)
      derivative
      (evaluatePolynomialDerivative coefficients)
      has-derivative
      (evaluatePolynomialHasDerivative coefficients)

evaluatePolynomialDerivativeValueUnique :
  ∀ coefficients x derivative-value →
  IsDerivativeAt
    (evaluatePolynomial coefficients)
    derivative-value x →
  derivative-value
    ≡ evaluatePolynomialDerivative coefficients x
evaluatePolynomialDerivativeValueUnique
  coefficients x derivative-value has-derivative =
    derivativeValueUniqueAt
      (evaluatePolynomial coefficients)
      x derivative-value
      (evaluatePolynomialDerivative coefficients x)
      has-derivative
      (isDerivativeAt
        (evaluatePolynomial coefficients)
        (evaluatePolynomialDerivative coefficients)
        (evaluatePolynomialHasDerivative coefficients)
        x)
