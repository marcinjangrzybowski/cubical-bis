module Cubical.Analysis.Real.Calculus.Derivative.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

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
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
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

  telescopingDifference :
    ∀ a b c → (a - b) + (b - c) ≡ a - c
  telescopingDifference a b c =
    addAssoc (a - b) b (- c)
    ∙ cong (_+ (- c)) (subAddCancel a b)

  chainDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' : A → ℝ)
      (outer outer' : ℝ → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (outer ∘ inner)
        (λ point → outer' (inner point) · inner' point)
        x y
      ≡
    derivativeErrorAlong
        (idfun ℝ) outer outer' (inner x) (inner y)
      +
    outer' (inner x) ·
      derivativeErrorAlong coordinate inner inner' x y
  chainDerivativeErrorPath
    coordinate inner inner' outer outer' x y =
      cong
        (λ value → outer-difference - value)
        (sym
          (mulAssoc
            (outer' (inner x)) (inner' x) displacement))
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' (inner x) · inner-difference)
          (outer' (inner x) · (inner' x · displacement)))
    ∙ cong
        (outer-error +_)
        (sym
          (ℝRing.·DistR-
            (outer' (inner x))
            inner-difference
            (inner' x · displacement)))
    where
    displacement : ℝ
    displacement = coordinate y - coordinate x

    inner-difference : ℝ
    inner-difference = inner y - inner x

    outer-difference : ℝ
    outer-difference = outer (inner y) - outer (inner x)

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        (idfun ℝ) outer outer' (inner x) (inner y)

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

  chainTotalErrorBound :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' : A → ℝ)
      (outer outer' : ℝ → ℝ)
      (x y : A) C G ε →
    absℝ (outer' (inner x)) ≤ℝ rat (fst G) →
    absℝ (inner y - inner x)
      ≤ℝ
    rat (fst C) · absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          (idfun ℝ) outer outer' (inner x) (inner y))
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ C)) ·
      absℝ (inner y - inner x) →
    absℝ
        (derivativeErrorAlong coordinate inner inner' x y)
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ G)) ·
      absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          coordinate
          (outer ∘ inner)
          (λ point → outer' (inner point) · inner' point)
          x y)
      ≤ℝ
    rat (fst ε) · absℝ (coordinate y - coordinate x)
  chainTotalErrorBound
    coordinate inner inner' outer outer'
    x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          absℝ error ≤ℝ rat (fst ε) · coordinate-distance)
        (sym
          (chainDerivativeErrorPath
            coordinate inner inner' outer outer' x y))
        (≤ℝ-trans
          (absℝ
            (outer-error + outer' (inner x) · inner-error))
          (absℝ outer-error +
            absℝ (outer' (inner x) · inner-error))
          (rat (fst ε) · coordinate-distance)
          (absTriangle
            outer-error
            (outer' (inner x) · inner-error))
          (subst
            ((absℝ outer-error +
              absℝ (outer' (inner x) · inner-error)) ≤ℝ_)
            half-sum-path
            (addPres≤
              (absℝ outer-error)
              (rat (fst (ε /2₊)) · coordinate-distance)
              (absℝ (outer' (inner x) · inner-error))
              (rat (fst (ε /2₊)) · coordinate-distance)
              (boundedErrorThroughLinearInput
                outer-error
                (absℝ (inner y - inner x))
                coordinate-distance C (ε /2₊)
                outer-error-bound inner-linear-bound)
              (boundedErrorProduct
                (outer' (inner x)) inner-error
                coordinate-distance G (ε /2₊)
                outer'-bound inner-error-bound))))
    where
    coordinate-distance : ℝ
    coordinate-distance = absℝ (coordinate y - coordinate x)

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        (idfun ℝ) outer outer' (inner x) (inner y)

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


-- The derivative of the inner map supplies both its local linear bound and
-- the continuity needed to pull the outer derivative neighbourhood back to
-- the parameter space.  All choices remain under propositional truncation.

chainHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' : A → ℝ)
    (outer outer' : ℝ → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate inner inner' →
  IsDerivative outer outer' →
  IsDerivativeAlong
    source coordinate
    (outer ∘ inner)
    (λ point → outer' (inner point) · inner' point)
chainHasDerivativeAlong
  source coordinate inner inner' outer outer'
  coordinate-continuous inner-derivative outer-derivative
  x ε = do
    (n , inner'-strict-bound) ← ∃naturalAbsBound (inner' x)
    (m , outer'-strict-bound) ←
      ∃naturalAbsBound (outer' (inner x))
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
      outer'-bound :
        absℝ (outer' (inner x)) ≤ℝ rat (fst G)
      outer'-bound =
        <ℝ-weaken
          (absℝ (outer' (inner x))) (rat (fst G))
          outer'-strict-bound
    (δlinear , inner-linear-near) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate inner inner'
        inner-derivative x B inner'-bound
    (δinner , inner-error-near) ←
      inner-derivative x ((ε /2₊) ₊／₊ G)
    (δouter , outer-error-near) ←
      outer-derivative
        (inner x) ((ε /2₊) ₊／₊ C)
    (δcomposition , inner-close-near) ←
      derivativeAlongIsContinuousAtBound
          source coordinate inner inner' x B
          inner'-bound
          (coordinate-continuous x)
          inner-derivative
        .IsContinuousAt.pres≈ δouter
    let
      δ : ℚ₊
      δ = min₊ δlinear (min₊ δinner δcomposition)
    return
      ( δ
      , λ y x≈δy →
          chainTotalErrorBound
            coordinate inner inner' outer outer'
            x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear
                  (min₊ δinner δcomposition))
                x≈δy))
            (outer-error-near (inner y)
              (inner-close-near y
                (PremetricStr.isMonotone≈≤
                  source x y δ δcomposition
                  (ℚ.isTrans≤
                    (fst δ)
                    (fst (min₊ δinner δcomposition))
                    (fst δcomposition)
                    (min₊≤R δlinear
                      (min₊ δinner δcomposition))
                    (min₊≤R δinner δcomposition))
                  x≈δy)))
            (inner-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δinner
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δinner δcomposition))
                  (fst δinner)
                  (min₊≤R δlinear
                    (min₊ δinner δcomposition))
                  (min₊≤L δinner δcomposition))
                x≈δy))
      )


chainHasDerivative :
  ∀ inner inner' outer outer' →
  IsDerivative inner inner' →
  IsDerivative outer outer' →
  IsDerivative
    (outer ∘ inner)
    (λ x → outer' (inner x) · inner' x)
chainHasDerivative inner inner' outer outer' =
  chainHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    inner inner' outer outer'
    (snd
      (CategoryStructures.idᶜ
        {M = ℝPremetricSpace}))
