module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative

open import Cubical.Relation.Premetric.Base

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  module ℚRing =
    RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  differenceOfSums :
    ∀ (a b c d : ℝ) →
    (a + b) - (c + d)
      ≡
    (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_)
      (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_)
        (addAssoc b (- c) (- d))
    ∙ cong (λ value → a + (value + (- d)))
        (addComm b (- c))
    ∙ cong (a +_)
        (sym (addAssoc (- c) b (- d)))
    ∙ addAssoc a (- c) (b + (- d))

  differenceOfNegatives :
    ∀ (a b : ℝ) →
    (- a) - (- b) ≡ - (a - b)
  differenceOfNegatives a b =
    cong ((- a) +_) (negInvol b)
    ∙ addComm (- a) b
    ∙ sym (negSub a b)

  derivativeErrorDifferencePath :
    ∀ (function : ℝ → ℝ) (x y a b : ℝ) →
    (function y - function x
        - b · (y - x))
      -
    (function y - function x
        - a · (y - x))
      ≡
    (a - b) · (y - x)
  derivativeErrorDifferencePath function x y a b =
    differenceOfSums
      difference (- (b · displacement))
      difference (- (a · displacement))
    ∙ cong₂ _+_
        (subSelf difference)
        (differenceOfNegatives
            (b · displacement)
            (a · displacement)
        ∙ negSub
            (b · displacement)
            (a · displacement))
    ∙ addIdL
        (a · displacement - b · displacement)
    ∙ sym (ℝRing.·DistL- a b displacement)
    where
    difference : ℝ
    difference = function y - function x

    displacement : ℝ
    displacement = y - x

  mulPositiveCancelR≤ :
    ∀ (a b c : ℝ) →
    0 <ℝ c →
    a · c ≤ℝ b · c →
    a ≤ℝ b
  mulPositiveCancelR≤ a b c 0<c ac≤bc =
    subst2 _≤ℝ_
      (positiveDivideMulCancel a c 0<c)
      (positiveDivideMulCancel b c 0<c)
      (mulMonoR≤
        (a · c) (b · c)
        (positiveReciprocal c 0<c)
        (<ℝ-weaken
          0 (positiveReciprocal c 0<c)
          (positiveReciprocalPositive c 0<c))
        ac≤bc)

  positiveIncrementDistance :
    ∀ (x : ℝ) (h : ℚ₊) →
    absℝ ((x + rat (fst h)) - x)
      ≡
    rat (fst h)
  positiveIncrementDistance x h =
    cong absℝ
      (cong (_- x)
          (addComm x (rat (fst h)))
      ∙ addSubCancel (rat (fst h)) x)
    ∙ abs-rat (fst h)
    ∙ cong rat
        (ℚOrder.0<→abs≡id (fst h) (snd h))

  zeroPositiveDistance :
    ∀ (h : ℚ₊) → abs (0 ℚ.- fst h) ≡ fst h
  zeroPositiveDistance h =
    ℚOrder.abs-Comm 0 (fst h)
    ∙ cong
        abs
        (cong
            (fst h ℚ.+_)
            ℚRing.0Selfinverse
        ∙ ℚ.+IdR (fst h))
    ∙ ℚOrder.0<→abs≡id
        (fst h) (snd h)

  closeToPositiveIncrement :
    ∀ (x : ℝ) (h δ : ℚ₊) →
    h <₊ δ →
    x ∼[ δ ] (x + rat (fst h))
  closeToPositiveIncrement x h δ h<δ =
    subst
      (λ left →
        left ∼[ δ ] (x + rat (fst h)))
      (addIdR x)
      (addPres∼₂
        x 0 (rat (fst h)) δ
        (rat-rat-fromAbs
          0 (fst h) δ
          (subst
            (ℚ._< fst δ)
            (sym (zeroPositiveDistance h))
            h<δ)))

  derivativeValuesCloseFromModuli :
    ∀ (function : ℝ → ℝ) (x a b : ℝ)
      (ε δa δb : ℚ₊) →
    (∀ y →
      x ∼[ δa ] y →
      absℝ
          (function y - function x
            - a · (y - x))
        ≤ℝ
      rat (fst (ε /4₊)) · absℝ (y - x)) →
    (∀ y →
      x ∼[ δb ] y →
      absℝ
          (function y - function x
            - b · (y - x))
        ≤ℝ
      rat (fst (ε /4₊)) · absℝ (y - x)) →
    a ∼[ ε ] b
  derivativeValuesCloseFromModuli
    function x a b ε δa δb
    a-error-near b-error-near =
      absDifference<→closeness a b ε
        (≤<ℝ-trans
          (absℝ (a - b))
          (rat (fst (ε /2₊)))
          (rat (fst ε))
          slope-difference-bound
          (<ℚ→<ℝ
            (fst (ε /2₊)) (fst ε)
            (/2₊<id ε)))
    where
    common : ℚ₊
    common = min₊ δa δb

    h : ℚ₊
    h = common /2₊

    y : ℝ
    y = x + rat (fst h)

    displacement : ℝ
    displacement = y - x

    distance : ℝ
    distance = absℝ displacement

    a-error b-error : ℝ
    a-error =
      function y - function x
        - a · displacement
    b-error =
      function y - function x
        - b · displacement

    h<δa : h <₊ δa
    h<δa =
      ℚ.isTrans<≤
        (fst h) (fst common) (fst δa)
        (/2₊<id common)
        (min₊≤L δa δb)

    h<δb : h <₊ δb
    h<δb =
      ℚ.isTrans<≤
        (fst h) (fst common) (fst δb)
        (/2₊<id common)
        (min₊≤R δa δb)

    a-error-bound :
      absℝ a-error
        ≤ℝ rat (fst (ε /4₊)) · distance
    a-error-bound =
      a-error-near y
        (closeToPositiveIncrement x h δa h<δa)

    b-error-bound :
      absℝ b-error
        ≤ℝ rat (fst (ε /4₊)) · distance
    b-error-bound =
      b-error-near y
        (closeToPositiveIncrement x h δb h<δb)

    half-bound-path :
      rat (fst (ε /4₊)) · distance
          + rat (fst (ε /4₊)) · distance
        ≡
      rat (fst (ε /2₊)) · distance
    half-bound-path =
      sym
        (mulDistL
          (rat (fst (ε /4₊)))
          (rat (fst (ε /4₊)))
          distance)
      ∙ cong
          (_· distance)
          (rat+rat
            (fst (ε /4₊))
            (fst (ε /4₊))
          ∙ cong rat
              (1/2∈ℚ./4+/4≡/2 (fst ε)))

    slope-product-bound :
      absℝ ((a - b) · displacement)
        ≤ℝ
      rat (fst (ε /2₊)) · distance
    slope-product-bound =
      subst
        (λ value →
          absℝ value
            ≤ℝ rat (fst (ε /2₊)) · distance)
        (derivativeErrorDifferencePath
          function x y a b)
        (≤ℝ-trans
          (absℝ (b-error - a-error))
          (absℝ b-error + absℝ a-error)
          (rat (fst (ε /2₊)) · distance)
          (absSubTriangle b-error a-error)
          (subst
            ((absℝ b-error + absℝ a-error) ≤ℝ_)
            half-bound-path
            (≤ℝ-add
              (absℝ b-error)
              (rat (fst (ε /4₊)) · distance)
              (absℝ a-error)
              (rat (fst (ε /4₊)) · distance)
              b-error-bound a-error-bound)))

    absolute-product-bound :
      absℝ (a - b) · distance
        ≤ℝ
      rat (fst (ε /2₊)) · distance
    absolute-product-bound =
      subst
        (_≤ℝ rat (fst (ε /2₊)) · distance)
        (absMul (a - b) displacement)
        slope-product-bound

    distance-positive : 0 <ℝ distance
    distance-positive =
      subst
        (0 <ℝ_)
        (sym (positiveIncrementDistance x h))
        (<ℚ→<ℝ 0 (fst h) (snd h))

    slope-difference-bound :
      absℝ (a - b) ≤ℝ rat (fst (ε /2₊))
    slope-difference-bound =
      mulPositiveCancelR≤
        (absℝ (a - b))
        (rat (fst (ε /2₊)))
        distance distance-positive
        absolute-product-bound

isPropIsDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  isProp
    (IsDerivativeAlong
      source coordinate function derivative)
isPropIsDerivativeAlong
  source coordinate function derivative =
    isPropΠ2 λ _ _ → squash₁

isPropIsDerivative :
  ∀ function derivative →
  isProp (IsDerivative function derivative)
isPropIsDerivative function derivative =
  isPropIsDerivativeAlong
    (snd ℝPremetricSpace)
    (idfun ℝ)
    function derivative

isPropIsDerivativeAt :
  ∀ function derivative-value x →
  isProp (IsDerivativeAt function derivative-value x)
isPropIsDerivativeAt function derivative-value x =
  isPropΠ λ _ → squash₁

derivativeValueUniqueAt :
  ∀ function x a b →
  IsDerivativeAt function a x →
  IsDerivativeAt function b x →
  a ≡ b
derivativeValueUniqueAt
  function x a b a-derivative b-derivative =
    PremetricStr.isSeparated≈
      (snd ℝPremetricSpace) a b λ ε →
        PT.rec
          (isProp∼ a ε b)
          (λ a-modulus →
            PT.rec
              (isProp∼ a ε b)
              (λ b-modulus →
                derivativeValuesCloseFromModuli
                  function x a b ε
                  (fst a-modulus) (fst b-modulus)
                  (snd a-modulus) (snd b-modulus))
              (b-derivative (ε /4₊)))
          (a-derivative (ε /4₊))

derivativeValueUnique :
  ∀ function derivative₁ derivative₂ →
  IsDerivative function derivative₁ →
  IsDerivative function derivative₂ →
  ∀ x → derivative₁ x ≡ derivative₂ x
derivativeValueUnique
  function derivative₁ derivative₂
  first-derivative second-derivative x =
    derivativeValueUniqueAt
      function x
      (derivative₁ x) (derivative₂ x)
      (first-derivative x)
      (second-derivative x)

derivativeFunctionUnique :
  ∀ function derivative₁ derivative₂ →
  IsDerivative function derivative₁ →
  IsDerivative function derivative₂ →
  derivative₁ ≡ derivative₂
derivativeFunctionUnique
  function derivative₁ derivative₂
  first-derivative second-derivative =
    funExt
      (derivativeValueUnique
        function derivative₁ derivative₂
        first-derivative second-derivative)

HasDerivative : (ℝ → ℝ) → Type
HasDerivative function =
  Σ[ derivative ∈ (ℝ → ℝ) ]
    IsDerivative function derivative

isPropHasDerivative :
  ∀ function → isProp (HasDerivative function)
isPropHasDerivative function
  (derivative₁ , first-derivative)
  (derivative₂ , second-derivative) =
    ΣPathPProp
      (isPropIsDerivative function)
      (derivativeFunctionUnique
        function derivative₁ derivative₂
        first-derivative second-derivative)

HasDerivativeAt : (ℝ → ℝ) → ℝ → Type
HasDerivativeAt function x =
  Σ[ derivative-value ∈ ℝ ]
    IsDerivativeAt function derivative-value x

isPropHasDerivativeAt :
  ∀ function x → isProp (HasDerivativeAt function x)
isPropHasDerivativeAt function x
  (a , a-derivative) (b , b-derivative) =
    ΣPathPProp
      (λ derivative-value →
        isPropIsDerivativeAt
          function derivative-value x)
      (derivativeValueUniqueAt
        function x a b a-derivative b-derivative)
