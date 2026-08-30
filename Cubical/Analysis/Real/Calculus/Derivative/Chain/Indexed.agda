module Cubical.Analysis.Real.Calculus.Derivative.Chain.Indexed where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Rational
  using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x

  telescopingDifference :
    ∀ a b c → (a - b) + (b - c) ≡ a - c
  telescopingDifference a b c =
    addAssoc (a - b) b (- c)
    ∙ cong (_+ (- c)) (subAddCancel a b)

  indexedChainDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' outer outer' : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate outer
        (λ point → outer' point · inner' point)
        x y
      ≡
    derivativeErrorAlong inner outer outer' x y
      + outer' x ·
          derivativeErrorAlong coordinate inner inner' x y
  indexedChainDerivativeErrorPath
    coordinate inner inner' outer outer' x y =
      cong
        (λ value → outer-difference - value)
        (sym (mulAssoc (outer' x) (inner' x) displacement))
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' x · inner-difference)
          (outer' x · (inner' x · displacement)))
    ∙ cong
        (outer-error +_)
        (sym
          (ℝRing.·DistR-
            (outer' x) inner-difference
            (inner' x · displacement)))
    where
    displacement : ℝ
    displacement = coordinate y - coordinate x

    inner-difference : ℝ
    inner-difference = inner y - inner x

    outer-difference : ℝ
    outer-difference = outer y - outer x

    outer-error : ℝ
    outer-error = derivativeErrorAlong inner outer outer' x y

  positiveRationalNonnegative :
    ∀ B → 0ℝ ≤ℝ rat (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      0ℝ (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  boundedErrorProduct :
    ∀ value error distance B ρ →
    absℝ value ≤ℝ rat (fst B) →
    absℝ error
      ≤ℝ rat (fst (ρ ₊／₊ B)) · distance →
    absℝ (value · error)
      ≤ℝ rat (fst ρ) · distance
  boundedErrorProduct
    value error distance B ρ
    absvalue≤B error-bound =
      subst
        (_≤ℝ rat (fst ρ) · distance)
        (sym (absMul value error))
        (subst
          ((absℝ value · absℝ error) ≤ℝ_)
          rational-product-path
          (mulPres≤
            (absℝ value) (rat (fst B))
            (absℝ error)
            (rat (fst (ρ ₊／₊ B)) · distance)
            (positiveRationalNonnegative B)
            (absNonnegative error)
            absvalue≤B error-bound))
    where
    rational-product-path :
      rat (fst B) ·
          (rat (fst (ρ ₊／₊ B)) · distance)
        ≡
      rat (fst ρ) · distance
    rational-product-path =
      mulAssoc
        (rat (fst B))
        (rat (fst (ρ ₊／₊ B))) distance
      ∙ cong
          (_· distance)
          (mul-rat (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat (·／ B ρ))

  boundedErrorThroughLinearInput :
    ∀ error input-distance coordinate-distance B ρ →
    absℝ error
      ≤ℝ rat (fst (ρ ₊／₊ B)) · input-distance →
    input-distance
      ≤ℝ rat (fst B) · coordinate-distance →
    absℝ error
      ≤ℝ rat (fst ρ) · coordinate-distance
  boundedErrorThroughLinearInput
    error input-distance coordinate-distance B ρ
    error-bound input-bound =
      ≤ℝ-trans
        (absℝ error)
        (rat (fst (ρ ₊／₊ B)) · input-distance)
        (rat (fst ρ) · coordinate-distance)
        error-bound
        (subst
          ((rat (fst (ρ ₊／₊ B)) · input-distance) ≤ℝ_)
          rational-product-path
          (mulPres≤L
            input-distance
            (rat (fst B) · coordinate-distance)
            (rat (fst (ρ ₊／₊ B)))
            (0≤→isNonnegative
              (rat (fst (ρ ₊／₊ B)))
              (positiveRationalNonnegative (ρ ₊／₊ B)))
            input-bound))
    where
    rational-product-path :
      rat (fst (ρ ₊／₊ B)) ·
          (rat (fst B) · coordinate-distance)
        ≡
      rat (fst ρ) · coordinate-distance
    rational-product-path =
      mulAssoc
        (rat (fst (ρ ₊／₊ B)))
        (rat (fst B)) coordinate-distance
      ∙ cong
          (_· coordinate-distance)
          (mulComm
              (rat (fst (ρ ₊／₊ B)))
              (rat (fst B))
          ∙ mul-rat (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat (·／ B ρ))

  indexedChainTotalErrorBound :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' outer outer' : A → ℝ)
      (x y : A) C G ε →
    absℝ (outer' x) ≤ℝ rat (fst G) →
    absℝ (inner y - inner x)
      ≤ℝ rat (fst C) · absℝ (coordinate y - coordinate x) →
    absℝ (derivativeErrorAlong inner outer outer' x y)
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ C)) ·
      absℝ (inner y - inner x) →
    absℝ (derivativeErrorAlong coordinate inner inner' x y)
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ G)) ·
      absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          coordinate outer
          (λ point → outer' point · inner' point)
          x y)
      ≤ℝ
    rat (fst ε) · absℝ (coordinate y - coordinate x)
  indexedChainTotalErrorBound
    coordinate inner inner' outer outer'
    x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          absℝ error ≤ℝ rat (fst ε) · coordinate-distance)
        (sym
          (indexedChainDerivativeErrorPath
            coordinate inner inner' outer outer' x y))
        (≤ℝ-trans
          (absℝ (outer-error + outer' x · inner-error))
          (absℝ outer-error + absℝ (outer' x · inner-error))
          (rat (fst ε) · coordinate-distance)
          (absTriangle outer-error (outer' x · inner-error))
          (subst
            ((absℝ outer-error +
              absℝ (outer' x · inner-error)) ≤ℝ_)
            half-sum-path
            (addPres≤
              (absℝ outer-error)
              (rat (fst (ε /2₊)) · coordinate-distance)
              (absℝ (outer' x · inner-error))
              (rat (fst (ε /2₊)) · coordinate-distance)
              (boundedErrorThroughLinearInput
                outer-error
                (absℝ (inner y - inner x))
                coordinate-distance C (ε /2₊)
                outer-error-bound inner-linear-bound)
              (boundedErrorProduct
                (outer' x) inner-error coordinate-distance
                G (ε /2₊) outer'-bound inner-error-bound))))
    where
    coordinate-distance : ℝ
    coordinate-distance = absℝ (coordinate y - coordinate x)

    outer-error : ℝ
    outer-error = derivativeErrorAlong inner outer outer' x y

    inner-error : ℝ
    inner-error =
      derivativeErrorAlong coordinate inner inner' x y

    half-sum-path :
      rat (fst (ε /2₊)) · coordinate-distance +
          rat (fst (ε /2₊)) · coordinate-distance
        ≡
      rat (fst ε) · coordinate-distance
    half-sum-path =
      sym
        (mulDistL
          (rat (fst (ε /2₊)))
          (rat (fst (ε /2₊)))
          coordinate-distance)
      ∙ cong
          (_· coordinate-distance)
          (rat+rat (fst (ε /2₊)) (fst (ε /2₊))
          ∙ cong rat (/2+/2≡id (fst ε)))


-- Both derivatives live on the same parameter space.  The outer derivative
-- is measured along the inner function, so no ambient extension is needed.

chainHasDerivativeAlongIndexed :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' outer outer' : A → ℝ) →
  IsDerivativeAlong source coordinate inner inner' →
  IsDerivativeAlong source inner outer outer' →
  IsDerivativeAlong
    source coordinate outer
    (λ point → outer' point · inner' point)
chainHasDerivativeAlongIndexed
  source coordinate inner inner' outer outer'
  inner-derivative outer-derivative x ε = do
    (n , inner'-strict-bound) ← ∃naturalAbsBound (inner' x)
    (m , outer'-strict-bound) ← ∃naturalAbsBound (outer' x)
    let
      B : ℚ₊
      B = naturalBound n
      C : ℚ₊
      C = 1₊ +₊ B
      G : ℚ₊
      G = naturalBound m
      inner'-bound : absℝ (inner' x) ≤ℝ rat (fst B)
      inner'-bound =
        <ℝ-weaken
          (absℝ (inner' x)) (rat (fst B))
          inner'-strict-bound
      outer'-bound : absℝ (outer' x) ≤ℝ rat (fst G)
      outer'-bound =
        <ℝ-weaken
          (absℝ (outer' x)) (rat (fst G))
          outer'-strict-bound
    (δlinear , inner-linear-near) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate inner inner'
        inner-derivative x B inner'-bound
    (δinner , inner-error-near) ←
      inner-derivative x ((ε /2₊) ₊／₊ G)
    (δouter , outer-error-near) ←
      outer-derivative x ((ε /2₊) ₊／₊ C)
    let
      δ : ℚ₊
      δ = min₊ δlinear (min₊ δinner δouter)
    return
      ( δ
      , λ y x∼y →
          indexedChainTotalErrorBound
            coordinate inner inner' outer outer'
            x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear (min₊ δinner δouter))
                x∼y))
            (outer-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δouter
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δinner δouter))
                  (fst δouter)
                  (min₊≤R δlinear (min₊ δinner δouter))
                  (min₊≤R δinner δouter))
                x∼y))
            (inner-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δinner
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δinner δouter))
                  (fst δinner)
                  (min₊≤R δlinear (min₊ δinner δouter))
                  (min₊≤L δinner δouter))
                x∼y))
      )
