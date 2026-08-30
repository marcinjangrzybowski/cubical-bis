module Cubical.Analysis.Real.Series.PowerSeries.Difference where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  productDifferencePath :
    ∀ x y p q →
    x · p - y · q
      ≡
    (x - y) · p + y · (p - q)
  productDifferencePath x y p q =
    cong (xp +_)
      (sym (addIdL (- yq)))
    ∙ cong (λ value → xp + (value + (- yq)))
        (sym (addInvL yp))
    ∙ addAssoc xp ((- yp) + yp) (- yq)
    ∙ cong (_+ (- yq))
        (addAssoc xp (- yp) yp)
    ∙ sym
        (addAssoc
          (xp + (- yp)) yp (- yq))
    ∙ cong₂ _+_
        (sym (ℝRing.·DistL- x y p))
        (sym (ℝRing.·DistR- y p q))
    where
    xp : ℝ
    xp = x · p

    yp : ℝ
    yp = y · p

    yq : ℝ
    yq = y · q

  commuteNestedProduct :
    ∀ a b c →
    a · (b · c) ≡ b · (a · c)
  commuteNestedProduct a b c =
    mulAssoc a b c
    ∙ cong (_· c) (mulComm a b)
    ∙ sym (mulAssoc b a c)

  collectSuccessorMultiple :
    ∀ coefficient value →
    value + coefficient · value
      ≡
    (coefficient + 1ℝ) · value
  collectSuccessorMultiple coefficient value =
    cong (_+ coefficient · value)
      (sym (mulIdL value))
    ∙ addComm
        (1ℝ · value)
        (coefficient · value)
    ∙ sym
        (mulDistL coefficient 1ℝ value)

  constant-isContinuous :
    ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (value : ℝ) →
    isContinuous source (λ (_ : A) → value)
      (ℝPremetricSpace .snd)
  constant-isContinuous source value =
    isNonExpanding→isContinuous
      source (λ _ → value) (ℝPremetricSpace .snd)
      λ where
        .IsNonExpanding.pres≈ _ _ ε _ →
          refl∼ value ε

  powerOfContinuousIsContinuous :
    ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (value : A → ℝ) →
    isContinuous source value (ℝPremetricSpace .snd) →
    ∀ n →
    isContinuous source
      (λ point → powℝ (value point) n)
      (ℝPremetricSpace .snd)
  powerOfContinuousIsContinuous
    source value value-continuous n =
    snd
      (CategoryStructures._∘C_
        ( (λ x → powℝ x n)
        , pow-isContinuous n
        )
        (value , value-continuous))


-- The finite geometric sum giving the divided difference of the power with
-- exponent suc n.  It is division-free and remains meaningful on x = y.

powerDifferenceFactor :
  ℝ → ℝ → ℕ → ℝ
powerDifferenceFactor x y zero =
  1ℝ
powerDifferenceFactor x y (suc n) =
  powℝ y (suc n)
    + x · powerDifferenceFactor x y n


powerDifferenceFactor-identity :
  ∀ x y n →
  powℝ y (suc n) - powℝ x (suc n)
    ≡
  (y - x) · powerDifferenceFactor x y n
powerDifferenceFactor-identity x y zero =
  cong₂ _-_
    (mulIdR y)
    (mulIdR x)
  ∙ sym (mulIdR (y - x))
powerDifferenceFactor-identity x y (suc n) =
  productDifferencePath
    y x (powℝ y (suc n)) (powℝ x (suc n))
  ∙ cong
      ((y - x) · powℝ y (suc n) +_)
      (cong
        (x ·_)
        (powerDifferenceFactor-identity x y n))
  ∙ cong
      ((y - x) · powℝ y (suc n) +_)
      (commuteNestedProduct
        x (y - x) (powerDifferenceFactor x y n))
  ∙ sym
      (mulDistR
        (y - x)
        (powℝ y (suc n))
        (x · powerDifferenceFactor x y n))


powerDifferenceFactor-diagonal :
  ∀ x n →
  powerDifferenceFactor x x n
    ≡
  realNatural (suc n) · powℝ x n
powerDifferenceFactor-diagonal x zero =
  sym realNatural-one
  ∙ sym (mulIdR (realNatural (suc zero)))
powerDifferenceFactor-diagonal x (suc n) =
  cong
    (λ value →
      powℝ x (suc n) + x · value)
    (powerDifferenceFactor-diagonal x n)
  ∙ cong
      (powℝ x (suc n) +_)
      (commuteNestedProduct
        x (realNatural (suc n)) (powℝ x n))
  ∙ collectSuccessorMultiple
      (realNatural (suc n)) (powℝ x (suc n))
  ∙ cong
      (_· powℝ x (suc n))
      (sym (realNatural-suc (suc n)))


powerDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x y : A → ℝ) →
  isContinuous source x (ℝPremetricSpace .snd) →
  isContinuous source y (ℝPremetricSpace .snd) →
  ∀ n →
  isContinuous source
    (λ point →
      powerDifferenceFactor (x point) (y point) n)
    (ℝPremetricSpace .snd)
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous zero =
  constant-isContinuous source 1ℝ
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous (suc n) =
  addOfContinuousIsContinuous
    source
    (λ point → powℝ (y point) (suc n))
    (λ point →
      x point ·
        powerDifferenceFactor (x point) (y point) n)
    (powerOfContinuousIsContinuous
      source y y-continuous (suc n))
    (mulOfContinuousIsContinuous
      source x
      (λ point →
        powerDifferenceFactor (x point) (y point) n)
      x-continuous
      (powerDifferenceFactorOfContinuousIsContinuous
        source x y x-continuous y-continuous n))


powerDifferenceFactor-bound :
  ∀ x y radius →
  0ℝ ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  ∀ n →
  absℝ (powerDifferenceFactor x y n)
    ≤ℝ
  realNatural (suc n) · powℝ radius n
powerDifferenceFactor-bound
  x y radius 0≤radius
  absx≤radius absy≤radius zero =
  subst
    (_≤ℝ
      realNatural (suc zero) · powℝ radius zero)
    (sym absOne)
    (subst
      (1ℝ ≤ℝ_)
      (sym target-is-one)
      (≤ℝ-refl 1ℝ))
  where
  target-is-one :
    realNatural (suc zero) · powℝ radius zero
      ≡
    1ℝ
  target-is-one =
    cong (_· 1ℝ) realNatural-one
    ∙ mulIdR 1ℝ
powerDifferenceFactor-bound
  x y radius 0≤radius
  absx≤radius absy≤radius (suc n) =
  ≤ℝ-trans
    (absℝ
      (powℝ y (suc n)
        + x · powerDifferenceFactor x y n))
    (absℝ (powℝ y (suc n))
      + absℝ (x · powerDifferenceFactor x y n))
    (realNatural (suc (suc n)) ·
      powℝ radius (suc n))
    (absTriangle
      (powℝ y (suc n))
      (x · powerDifferenceFactor x y n))
    (subst
      ((absℝ (powℝ y (suc n))
        + absℝ (x · powerDifferenceFactor x y n)) ≤ℝ_)
      sum-bound-path
      (addPres≤
        (absℝ (powℝ y (suc n)))
        (powℝ radius (suc n))
        (absℝ (x · powerDifferenceFactor x y n))
        (radius ·
          (realNatural (suc n) · powℝ radius n))
        power-bound product-bound))
  where
  power-bound :
    absℝ (powℝ y (suc n))
      ≤ℝ
    powℝ radius (suc n)
  power-bound =
    subst
      (_≤ℝ powℝ radius (suc n))
      (sym (absPow y (suc n)))
      (powMono (suc n) (absNonnegative y) absy≤radius)

  product-bound :
    absℝ (x · powerDifferenceFactor x y n)
      ≤ℝ
    radius ·
      (realNatural (suc n) · powℝ radius n)
  product-bound =
    subst
      (_≤ℝ
        radius ·
          (realNatural (suc n) · powℝ radius n))
      (sym
        (absMul x (powerDifferenceFactor x y n)))
      (mulPres≤
        (absℝ x) radius
        (absℝ (powerDifferenceFactor x y n))
        (realNatural (suc n) · powℝ radius n)
        0≤radius
        (absNonnegative (powerDifferenceFactor x y n))
        absx≤radius
        (powerDifferenceFactor-bound
          x y radius 0≤radius
          absx≤radius absy≤radius n))

  sum-bound-path :
    powℝ radius (suc n)
        + radius ·
          (realNatural (suc n) · powℝ radius n)
      ≡
    realNatural (suc (suc n)) ·
      powℝ radius (suc n)
  sum-bound-path =
    cong
      (powℝ radius (suc n) +_)
      (commuteNestedProduct
        radius (realNatural (suc n)) (powℝ radius n))
    ∙ collectSuccessorMultiple
        (realNatural (suc n)) (powℝ radius (suc n))
    ∙ cong
        (_· powℝ radius (suc n))
        (sym (realNatural-suc (suc n)))


powerSeriesDifferenceFactor :
  RealSequence → ℝ → ℝ → RealSequence
powerSeriesDifferenceFactor coefficients x y n =
  coefficients (suc n) ·
    powerDifferenceFactor x y n


powerSeriesDifferenceFactor-identity :
  ∀ coefficients x y n →
  powerSeriesTerms coefficients y (suc n)
      - powerSeriesTerms coefficients x (suc n)
    ≡
  (y - x) ·
    powerSeriesDifferenceFactor coefficients x y n
powerSeriesDifferenceFactor-identity
  coefficients x y n =
  sym
    (ℝRing.·DistR-
      (coefficients (suc n))
      (powℝ y (suc n))
      (powℝ x (suc n)))
  ∙ cong
      (coefficients (suc n) ·_)
      (powerDifferenceFactor-identity x y n)
  ∙ commuteNestedProduct
      (coefficients (suc n))
      (y - x)
      (powerDifferenceFactor x y n)


powerSeriesDifferenceFactor-diagonal-term :
  ∀ coefficients x n →
  powerSeriesDifferenceFactor coefficients x x n
    ≡
  powerSeriesTerms (formalDerivative coefficients) x n
powerSeriesDifferenceFactor-diagonal-term
  coefficients x n =
  cong
    (coefficients (suc n) ·_)
    (powerDifferenceFactor-diagonal x n)
  ∙ commuteNestedProduct
      (coefficients (suc n))
      (realNatural (suc n))
      (powℝ x n)
  ∙ mulAssoc
      (realNatural (suc n))
      (coefficients (suc n))
      (powℝ x n)


powerSeriesDifferenceFactor-diagonal :
  ∀ coefficients x →
  powerSeriesDifferenceFactor coefficients x x
    ≡
  powerSeriesTerms (formalDerivative coefficients) x
powerSeriesDifferenceFactor-diagonal coefficients x =
  funExt
    (powerSeriesDifferenceFactor-diagonal-term
      coefficients x)


powerSeriesDifferenceFactorTermBoundByDerivativeMajorant :
  ∀ coefficients majorant x y radius →
  CoefficientMajorizedBy coefficients majorant →
  0ℝ ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  ∀ n →
  absℝ
      (powerSeriesDifferenceFactor coefficients x y n)
    ≤ℝ
  powerSeriesTerms
    (formalDerivativeMajorant majorant) radius n
powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
  coefficients majorant x y radius
  majorized 0≤radius absx≤radius absy≤radius n =
  subst2 _≤ℝ_
    (sym
      (absMul
        (coefficients (suc n))
        (powerDifferenceFactor x y n)))
    target-path
    (mulPres≤
      (absℝ (coefficients (suc n)))
      (majorant (suc n))
      (absℝ (powerDifferenceFactor x y n))
      (realNatural (suc n) · powℝ radius n)
      (coefficientMajorantIsNonnegative
        coefficients majorant majorized (suc n))
      (absNonnegative (powerDifferenceFactor x y n))
      (majorized (suc n))
      (powerDifferenceFactor-bound
        x y radius 0≤radius
        absx≤radius absy≤radius n))
  where
  target-path :
    majorant (suc n) ·
        (realNatural (suc n) · powℝ radius n)
      ≡
    powerSeriesTerms
      (formalDerivativeMajorant majorant) radius n
  target-path =
    commuteNestedProduct
      (majorant (suc n))
      (realNatural (suc n))
      (powℝ radius n)
    ∙ mulAssoc
        (realNatural (suc n))
        (majorant (suc n))
        (powℝ radius n)


powerSeriesDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    coefficients
    (x y : A → ℝ) →
  isContinuous source x (ℝPremetricSpace .snd) →
  isContinuous source y (ℝPremetricSpace .snd) →
  ∀ n →
  isContinuous source
    (λ point →
      powerSeriesDifferenceFactor
        coefficients (x point) (y point) n)
    (ℝPremetricSpace .snd)
powerSeriesDifferenceFactorOfContinuousIsContinuous
  source coefficients x y
  x-continuous y-continuous n =
  mulOfContinuousIsContinuous
    source
    (λ _ → coefficients (suc n))
    (λ point →
      powerDifferenceFactor (x point) (y point) n)
    (constant-isContinuous
      source (coefficients (suc n)))
    (powerDifferenceFactorOfContinuousIsContinuous
      source x y x-continuous y-continuous n)
