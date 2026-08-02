module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  productDifferencePath :
    ∀ x y p q →
    x · p - y · q
      ≡
    (x - y) · p + y · (p - q)
  productDifferencePath x y p q =
    cong (xp +_)
      (sym (addIdL (- yq)))
    ∙ cong (λ z → xp + (z + (- yq)))
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

  differenceOfSums :
    ∀ a b c d →
    (a + b) - (c + d)
      ≡
    (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_)
      (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_)
        (addAssoc b (- c) (- d))
    ∙ cong (λ z → a + (z + (- d)))
        (addComm b (- c))
    ∙ cong (a +_)
        (sym (addAssoc (- c) b (- d)))
    ∙ addAssoc a (- c) (b + (- d))

  commuteNestedProduct :
    ∀ a b c →
    a · (b · c) ≡ b · (a · c)
  commuteNestedProduct a b c =
    sym (mulAssoc a b c)
    ∙ cong (_· c) (mulComm a b)
    ∙ mulAssoc b a c

  collectSuccessorMultiple :
    ∀ coefficient value →
    value + coefficient · value
      ≡
    (coefficient + 1) · value
  collectSuccessorMultiple coefficient value =
    cong (_+ coefficient · value)
      (sym (mulIdL value))
    ∙ addComm
        (1 · value)
        (coefficient · value)
    ∙ sym
        (mulDistL coefficient 1 value)

-- The divided-difference polynomial for the power with exponent `suc n`.
-- The recurrence is the finite geometric sum, oriented so its diagonal is
-- definitionally aligned with the formal coefficient derivative.
powerDifferenceFactor :
  ℝ → ℝ → ℕ → ℝ
powerDifferenceFactor x y zero =
  1
powerDifferenceFactor x y (suc n) =
  y ^ⁿ suc n
    + x · powerDifferenceFactor x y n

powerDifferenceFactor-identity :
  ∀ x y n →
  y ^ⁿ suc n - x ^ⁿ suc n
    ≡
  (y - x) · powerDifferenceFactor x y n
powerDifferenceFactor-identity x y zero =
  cong₂ _-_
    (mulIdR y)
    (mulIdR x)
  ∙ sym (mulIdR (y - x))
powerDifferenceFactor-identity
  x y (suc n) =
    productDifferencePath
      y x
      (y ^ⁿ suc n)
      (x ^ⁿ suc n)
    ∙ cong
        ((y - x) · y ^ⁿ suc n +_)
        (cong (x ·_)
          (powerDifferenceFactor-identity
            x y n))
    ∙ cong
        ((y - x) · y ^ⁿ suc n +_)
        (commuteNestedProduct
          x (y - x)
          (powerDifferenceFactor x y n))
    ∙ sym
        (mulDistR
          (y - x)
          (y ^ⁿ suc n)
          (x · powerDifferenceFactor x y n))

powerDifferenceFactor-diagonal :
  ∀ x n →
  powerDifferenceFactor x x n
    ≡
  realNatural (suc n) · x ^ⁿ n
powerDifferenceFactor-diagonal x zero =
  sym (addIdL 1)
  ∙ sym
      (mulIdR
        (realNatural (suc zero)))
powerDifferenceFactor-diagonal x (suc n) =
  cong
    (λ value →
      x ^ⁿ suc n + x · value)
    (powerDifferenceFactor-diagonal x n)
  ∙ cong
      (x ^ⁿ suc n +_)
      (commuteNestedProduct
        x (realNatural (suc n))
        (x ^ⁿ n))
  ∙ collectSuccessorMultiple
      (realNatural (suc n))
      (x ^ⁿ suc n)

powerDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x y : A → ℝ) →
  isContinuous source x
    (snd ℝPremetricSpace) →
  isContinuous source y
    (snd ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ point →
      powerDifferenceFactor
        (x point) (y point) n)
    (snd ℝPremetricSpace)
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous zero point
  .IsContinuousAt.pres≈ ε =
    return
      ( 1
      , λ _ _ → refl∼ 1 ε
      )
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous (suc n) =
    addOfContinuousIsContinuous
      source
      (λ point → y point ^ⁿ suc n)
      (λ point →
        x point
          · powerDifferenceFactor
              (x point) (y point) n)
      (powerOfContinuousIsContinuous
        source y y-continuous (suc n))
      (mulOfContinuousIsContinuous
        source
        x
        (λ point →
          powerDifferenceFactor
            (x point) (y point) n)
        x-continuous
        (powerDifferenceFactorOfContinuousIsContinuous
          source x y
          x-continuous y-continuous n))

powerDifferenceFactor-bound :
  ∀ x y radius →
  0 ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  ∀ n →
  absℝ (powerDifferenceFactor x y n)
    ≤ℝ
  realNatural (suc n) · radius ^ⁿ n
powerDifferenceFactor-bound
  x y radius 0≤radius
  absx≤radius absy≤radius zero =
    subst
      (_≤ℝ
        realNatural (suc zero)
          · radius ^ⁿ zero)
      (sym absOne)
      (subst
        (1 ≤ℝ_)
        (sym target-is-one)
        (≤ℝ-refl 1))
  where
  target-is-one :
    realNatural (suc zero)
        · radius ^ⁿ zero
      ≡
    1
  target-is-one =
    cong (_· 1) (addIdL 1)
    ∙ mulIdR 1
powerDifferenceFactor-bound
  x y radius 0≤radius
  absx≤radius absy≤radius (suc n) =
    ≤ℝ-trans
      (absℝ
        (y ^ⁿ suc n
          + x · powerDifferenceFactor x y n))
      (absℝ (y ^ⁿ suc n)
        + absℝ
            (x · powerDifferenceFactor x y n))
      (realNatural (suc (suc n))
        · radius ^ⁿ suc n)
      (absTriangle
        (y ^ⁿ suc n)
        (x · powerDifferenceFactor x y n))
      (subst
        ((absℝ (y ^ⁿ suc n)
          + absℝ
              (x · powerDifferenceFactor x y n))
          ≤ℝ_)
        sum-bound-path
        (≤ℝ-add
          (absℝ (y ^ⁿ suc n))
          (radius ^ⁿ suc n)
          (absℝ
            (x · powerDifferenceFactor x y n))
          (radius
            · (realNatural (suc n)
              · radius ^ⁿ n))
          power-bound
          product-bound))
  where
  power-bound :
    absℝ (y ^ⁿ suc n)
      ≤ℝ
    radius ^ⁿ suc n
  power-bound =
    subst
      (_≤ℝ radius ^ⁿ suc n)
      (sym (absPow (suc n) y))
      (powMonoℝ
        (suc n)
        (absNonnegative y)
        absy≤radius)

  product-bound :
    absℝ
        (x · powerDifferenceFactor x y n)
      ≤ℝ
    radius
      · (realNatural (suc n)
        · radius ^ⁿ n)
  product-bound =
    subst
      (_≤ℝ
        radius
          · (realNatural (suc n)
            · radius ^ⁿ n))
      (sym
        (absMul x
          (powerDifferenceFactor x y n)))
      (mulMono≤
        (absℝ x) radius
        (absℝ (powerDifferenceFactor x y n))
        (realNatural (suc n)
          · radius ^ⁿ n)
        0≤radius
        (absNonnegative
          (powerDifferenceFactor x y n))
        absx≤radius
        (powerDifferenceFactor-bound
          x y radius 0≤radius
          absx≤radius absy≤radius n))

  sum-bound-path :
    radius ^ⁿ suc n
        + radius
          · (realNatural (suc n)
            · radius ^ⁿ n)
      ≡
    realNatural (suc (suc n))
      · radius ^ⁿ suc n
  sum-bound-path =
    cong
      (radius ^ⁿ suc n +_)
      (commuteNestedProduct
        radius (realNatural (suc n))
        (radius ^ⁿ n))
    ∙ collectSuccessorMultiple
        (realNatural (suc n))
        (radius ^ⁿ suc n)

powerSeriesDifferenceFactor :
  RealSequence → ℝ → ℝ → RealSequence
powerSeriesDifferenceFactor
  coefficients x y n =
    coefficients (suc n)
      · powerDifferenceFactor x y n

powerSeriesDifferenceFactorTermBoundByDerivativeMajorant :
  ∀ coefficients majorant x y radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  0 ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  ∀ n →
  absℝ
      (powerSeriesDifferenceFactor
        coefficients x y n)
    ≤ℝ
  powerSeriesTerms
    (formalDerivativeMajorant majorant)
    radius n
powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
  coefficients majorant x y radius
  majorized nonnegative 0≤radius
  absx≤radius absy≤radius n =
    subst2 _≤ℝ_
      (sym
        (absMul
          (coefficients (suc n))
          (powerDifferenceFactor x y n)))
      target-path
      (mulMono≤
        (absℝ (coefficients (suc n)))
        (majorant (suc n))
        (absℝ (powerDifferenceFactor x y n))
        (realNatural (suc n)
          · radius ^ⁿ n)
        (nonnegative (suc n))
        (absNonnegative
          (powerDifferenceFactor x y n))
        (majorized (suc n))
        (powerDifferenceFactor-bound
          x y radius 0≤radius
          absx≤radius absy≤radius n))
  where
  target-path :
    majorant (suc n)
        · (realNatural (suc n)
          · radius ^ⁿ n)
      ≡
    powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius n
  target-path =
    commuteNestedProduct
      (majorant (suc n))
      (realNatural (suc n))
      (radius ^ⁿ n)
    ∙ sym
        (mulAssoc
          (realNatural (suc n))
          (majorant (suc n))
          (radius ^ⁿ n))

powerSeriesDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    coefficients
    (x y : A → ℝ) →
  isContinuous source x
    (snd ℝPremetricSpace) →
  isContinuous source y
    (snd ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ point →
      powerSeriesDifferenceFactor
        coefficients
        (x point) (y point) n)
    (snd ℝPremetricSpace)
powerSeriesDifferenceFactorOfContinuousIsContinuous
  source coefficients x y
  x-continuous y-continuous n =
    mulOfContinuousIsContinuous
      source
      (λ _ → coefficients (suc n))
      (λ point →
        powerDifferenceFactor
          (x point) (y point) n)
      constant-continuous
      (powerDifferenceFactorOfContinuousIsContinuous
        source x y
        x-continuous y-continuous n)
  where
  constant-continuous :
    isContinuous source
      (λ _ → coefficients (suc n))
      (snd ℝPremetricSpace)
  constant-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( 1
        , λ _ _ →
            refl∼ (coefficients (suc n)) ε
        )

powerSeriesDifferenceFactor-diagonal :
  ∀ coefficients x →
  powerSeriesDifferenceFactor
      coefficients x x
    ≡
  powerSeriesTerms
    (formalDerivative coefficients)
    x
powerSeriesDifferenceFactor-diagonal
  coefficients x =
    funExt
      (λ n →
        cong
          (coefficients (suc n) ·_)
          (powerDifferenceFactor-diagonal
            x n)
        ∙ commuteNestedProduct
            (coefficients (suc n))
            (realNatural (suc n))
            (x ^ⁿ n)
        ∙ sym
            (mulAssoc
              (realNatural (suc n))
              (coefficients (suc n))
              (x ^ⁿ n)))

finitePowerSeriesDifference :
  ∀ coefficients x y n →
  partialSum
      (powerSeriesTerms coefficients y)
      (suc n)
    -
  partialSum
      (powerSeriesTerms coefficients x)
      (suc n)
    ≡
  (y - x)
    · partialSum
        (powerSeriesDifferenceFactor
          coefficients x y)
        n
finitePowerSeriesDifference
  coefficients x y zero =
    cong₂ _-_
      (addIdL
        (coefficients zero · y ^ⁿ zero)
      ∙ mulIdR (coefficients zero))
      (addIdL
        (coefficients zero · x ^ⁿ zero)
      ∙ mulIdR (coefficients zero))
    ∙ subSelf (coefficients zero)
    ∙ sym (mulZeroR (y - x))
finitePowerSeriesDifference
  coefficients x y (suc n) =
    differenceOfSums
      (partialSum
        (powerSeriesTerms coefficients y)
        (suc n))
      (powerSeriesTerms
        coefficients y (suc n))
      (partialSum
        (powerSeriesTerms coefficients x)
        (suc n))
      (powerSeriesTerms
        coefficients x (suc n))
    ∙ cong₂ _+_
        (finitePowerSeriesDifference
          coefficients x y n)
        term-difference
    ∙ sym
        (mulDistR
          (y - x)
          (partialSum
            (powerSeriesDifferenceFactor
              coefficients x y)
            n)
          (powerSeriesDifferenceFactor
            coefficients x y n))
  where
  term-difference :
    powerSeriesTerms
        coefficients y (suc n)
      -
    powerSeriesTerms
        coefficients x (suc n)
      ≡
    (y - x)
      · powerSeriesDifferenceFactor
          coefficients x y n
  term-difference =
    sym
      (ℝRing.·DistR-
        (coefficients (suc n))
        (y ^ⁿ suc n)
        (x ^ⁿ suc n))
    ∙ cong
        (coefficients (suc n) ·_)
        (powerDifferenceFactor-identity
          x y n)
    ∙ commuteNestedProduct
        (coefficients (suc n))
        (y - x)
        (powerDifferenceFactor x y n)
