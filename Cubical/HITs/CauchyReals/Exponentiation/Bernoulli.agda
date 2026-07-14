module Cubical.HITs.CauchyReals.Exponentiation.Bernoulli where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)

open import Cubical.HITs.CauchyReals.Exponentiation.Core
open import Cubical.HITs.CauchyReals.Exponentiation.Convexity

private
  zeroToOne : 0 ℚ.< 1
  zeroToOne = ℚ.decℚ<?

  opaque
    multiplyStrictPositive :
      (left right : ℝ) (positive : ℝ₊) →
      left <ᵣ right →
      fst positive ·ᵣ left <ᵣ fst positive ·ᵣ right
    multiplyStrictPositive left right positive =
      <ᵣ-o·ᵣ left right positive

    cancelPositiveRight :
      (numerator : ℝ) (denominator : ℝ₊) →
      fst denominator ·ᵣ
        (numerator ·ᵣ fst (invℝ₊ denominator)) ≡ numerator
    cancelPositiveRight numerator denominator =
      ·ᵣComm
        (fst denominator)
        (numerator ·ᵣ fst (invℝ₊ denominator))
      ∙ [x/₊y]·yᵣ numerator denominator

opaque
  unfolding invℝ powerSecantSlope
  bernoulli's-ineq-^ℚ-r<1 :
    ∀ x r → 1 <ᵣ fst x → 0 ℚ.< r → r ℚ.< 1 →
    fst (x ^ℚ r) <ᵣ 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)
  bernoulli's-ineq-^ℚ-r<1 x r 1<x 0<r r<1 =
    isTrans<≡ᵣ
      (fst (x ^ℚ r))
      (rat r ·ᵣ (fst x -ᵣ 1) +ᵣ 1)
      (1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1))
      addBound
      (+ᵣComm (rat r ·ᵣ (fst x -ᵣ 1)) 1)
    where
    strictSlope :
      ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) <ᵣ
      ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))
    strictSlope =
      slope-zero-one-strict-below x 1<x r 0<r r<1 zeroToOne

    secantR : ℝ
    secantR = powerSecantSlope 0 r 0<r (fst x) (snd x)

    intervalR : ℝ₊
    intervalR = ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)

    differenceR : ℝ
    differenceR = fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0)

    secantOne : ℝ
    secantOne = powerSecantSlope 0 1 zeroToOne (fst x) (snd x)

    secantRFormula :
      secantR ≡
      ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r))
    secantRFormula =
      refl

    secantOneFormula :
      secantOne ≡
      ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))
    secantOneFormula =
      refl

    abstractStrictSlope : secantR <ᵣ secantOne
    abstractStrictSlope =
      strictSlope

    multipliedAbstract :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ secantR <ᵣ
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ secantOne
    multipliedAbstract =
      multiplyStrictPositive secantR secantOne
        (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) abstractStrictSlope

    multipliedBound :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) <ᵣ
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))
    multipliedBound =
      multipliedAbstract

    cancelAbstract : fst intervalR ·ᵣ secantR ≡ differenceR
    cancelAbstract = cancelPositiveRight differenceR intervalR

    cancelLeftPath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ≡
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0)
    cancelLeftPath = cancelAbstract

    unscaledBound :
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0) <ᵣ
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))
    unscaledBound =
      subst2 (λ left right → left <ᵣ right)
        cancelLeftPath refl multipliedBound

    zeroPowerPath : fst (x ^ℚ 0) ≡ 1
    zeroPowerPath = cong fst (^ℚ-zero x)

    onePowerPath : fst (x ^ℚ 1) ≡ fst x
    onePowerPath = cong fst (^ℚ-1 x)

    differenceRPath :
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0) ≡
      fst (x ^ℚ r) -ᵣ 1
    differenceRPath =
      cong (λ y → fst (x ^ℚ r) -ᵣ y) zeroPowerPath

    intervalRPath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ≡ rat r
    intervalRPath = cong rat ℚ!

    intervalOnePath :
      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne) ≡ 1
    intervalOnePath = ℝ₊≡ (cong rat ℚ!)

    intervalOneInversePath :
      fst
        (invℝ₊
          (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))) ≡ 1
    intervalOneInversePath =
      cong (fst ∘ invℝ₊) intervalOnePath ∙ cong fst invℝ₊1

    oneDifferencePath :
      fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0) ≡ fst x -ᵣ 1
    oneDifferencePath = cong₂ _-ᵣ_ onePowerPath zeroPowerPath

    slopeOnePath :
      ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) ≡
      fst x -ᵣ 1
    slopeOnePath =
      cong₂ _·ᵣ_ oneDifferencePath intervalOneInversePath
      ∙ ·IdR (fst x -ᵣ 1)

    scaledSlopePath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) ≡
      rat r ·ᵣ (fst x -ᵣ 1)
    scaledSlopePath = cong₂ _·ᵣ_ intervalRPath slopeOnePath

    normalizedBound :
      fst (x ^ℚ r) -ᵣ 1 <ᵣ rat r ·ᵣ (fst x -ᵣ 1)
    normalizedBound =
      subst2 (λ left right → left <ᵣ right)
        differenceRPath scaledSlopePath unscaledBound

    addBound :
      fst (x ^ℚ r) <ᵣ rat r ·ᵣ (fst x -ᵣ 1) +ᵣ 1
    addBound =
      a-b<c⇒a<c+b (fst (x ^ℚ r)) 1
        (rat r ·ᵣ (fst x -ᵣ 1)) normalizedBound

  bernoulli's-ineq-^ℚ :
    ∀ x r → 1 <ᵣ fst x → 1 ℚ.< r →
    1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1) <ᵣ fst (x ^ℚ r)
  bernoulli's-ineq-^ℚ x r 1<x 1<r =
    isTrans≡<ᵣ
      (1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1))
      (rat r ·ᵣ (fst x -ᵣ 1) +ᵣ 1)
      (fst (x ^ℚ r))
      (+ᵣComm 1 (rat r ·ᵣ (fst x -ᵣ 1))) addBound
    where
    0<r : 0 ℚ.< r
    0<r = ℚ.isTrans< 0 1 r zeroToOne 1<r

    strictSlope :
      ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) <ᵣ
      ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r))
    strictSlope =
      slope-zero-one-strict-above x 1<x r zeroToOne 1<r 0<r

    secantR : ℝ
    secantR = powerSecantSlope 0 r 0<r (fst x) (snd x)

    secantOne : ℝ
    secantOne = powerSecantSlope 0 1 zeroToOne (fst x) (snd x)

    intervalR : ℝ₊
    intervalR = ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)

    differenceR : ℝ
    differenceR = fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0)

    abstractStrictSlope : secantOne <ᵣ secantR
    abstractStrictSlope = strictSlope

    multipliedAbstract :
      fst intervalR ·ᵣ secantOne <ᵣ fst intervalR ·ᵣ secantR
    multipliedAbstract =
      multiplyStrictPositive secantOne secantR intervalR
        abstractStrictSlope

    multipliedBound :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) <ᵣ
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r))
    multipliedBound = multipliedAbstract

    cancelRightPath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ≡
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0)
    cancelRightPath = cancelPositiveRight differenceR intervalR

    unscaledAbstract :
      fst intervalR ·ᵣ secantOne <ᵣ differenceR
    unscaledAbstract =
      isTrans<≡ᵣ
        (fst intervalR ·ᵣ secantOne)
        (fst intervalR ·ᵣ secantR)
        differenceR
        multipliedAbstract cancelRightPath

    unscaledBound :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) <ᵣ
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0)
    unscaledBound =
      unscaledAbstract

    zeroPowerPath : fst (x ^ℚ 0) ≡ 1
    zeroPowerPath = cong fst (^ℚ-zero x)

    onePowerPath : fst (x ^ℚ 1) ≡ fst x
    onePowerPath = cong fst (^ℚ-1 x)

    differenceRPath :
      fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0) ≡
      fst (x ^ℚ r) -ᵣ 1
    differenceRPath =
      cong (λ y → fst (x ^ℚ r) -ᵣ y) zeroPowerPath

    intervalRPath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ≡ rat r
    intervalRPath = cong rat ℚ!

    intervalOnePath :
      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne) ≡ 1
    intervalOnePath = ℝ₊≡ (cong rat ℚ!)

    intervalOneInversePath :
      fst
        (invℝ₊
          (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne))) ≡ 1
    intervalOneInversePath =
      cong (fst ∘ invℝ₊) intervalOnePath ∙ cong fst invℝ₊1

    oneDifferencePath :
      fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0) ≡ fst x -ᵣ 1
    oneDifferencePath = cong₂ _-ᵣ_ onePowerPath zeroPowerPath

    slopeOnePath :
      ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) ≡
      fst x -ᵣ 1
    slopeOnePath =
      cong₂ _·ᵣ_ oneDifferencePath intervalOneInversePath
      ∙ ·IdR (fst x -ᵣ 1)

    scaledSlopePath :
      fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
        ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 zeroToOne)) ≡
      rat r ·ᵣ (fst x -ᵣ 1)
    scaledSlopePath = cong₂ _·ᵣ_ intervalRPath slopeOnePath

    normalizedBound :
      rat r ·ᵣ (fst x -ᵣ 1) <ᵣ fst (x ^ℚ r) -ᵣ 1
    normalizedBound =
      subst2 (λ left right → left <ᵣ right)
        scaledSlopePath differenceRPath unscaledBound

    addBound :
      rat r ·ᵣ (fst x -ᵣ 1) +ᵣ 1 <ᵣ fst (x ^ℚ r)
    addBound =
      a<b-c⇒a+c<b (rat r ·ᵣ (fst x -ᵣ 1))
        (fst (x ^ℚ r)) 1 normalizedBound
