module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  telescopingDifference :
    ∀ a b c →
    (a - b) + (b - c) ≡ a - c
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
        (λ point → outer (inner point))
        (λ point → outer' (inner point) · inner' point)
        x y
      ≡
    derivativeErrorAlong
        (λ value → value) outer outer'
        (inner x) (inner y)
      + outer' (inner x)
          · derivativeErrorAlong
              coordinate inner inner' x y
  chainDerivativeErrorPath
    coordinate inner inner' outer outer' x y =
      cong
        (λ value → outer-difference - value)
        (mulAssoc
          (outer' (inner x))
          (inner' x)
          displacement)
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' (inner x) · inner-difference)
          (outer' (inner x)
            · (inner' x · displacement)))
    ∙ cong
        (outer-error +_)
        (sym
          (ℝRing.·DistR-
            (outer' (inner x))
            inner-difference
            (inner' x · displacement)))
    where
    displacement : ℝ
    displacement =
      coordinate y - coordinate x

    inner-difference : ℝ
    inner-difference =
      inner y - inner x

    outer-difference : ℝ
    outer-difference =
      outer (inner y) - outer (inner x)

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        (λ value → value) outer outer'
        (inner x) (inner y)

  positiveRationalNonnegative :
    ∀ B → 0 ≤ℝ rat (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      0 (rat (fst B))
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
          (mulMono≤
            (absℝ value) (rat (fst B))
            (absℝ error)
            (rat (fst (ρ ₊／₊ B)) · distance)
            (positiveRationalNonnegative B)
            (absNonnegative error)
            absvalue≤B error-bound))
    where
    rational-product-path :
      rat (fst B)
          · (rat (fst (ρ ₊／₊ B)) · distance)
        ≡
      rat (fst ρ) · distance
    rational-product-path =
      sym
        (mulAssoc
          (rat (fst B))
          (rat (fst (ρ ₊／₊ B)))
          distance)
      ∙ cong
          (_· distance)
          (mul-rat
            (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat (·／ B ρ))

  boundedErrorThroughLinearInput :
    ∀ error input-distance coordinate-distance B ρ →
    absℝ error
      ≤ℝ
    rat (fst (ρ ₊／₊ B)) · input-distance →
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
          (mulMonoL≤
            input-distance
            (rat (fst B) · coordinate-distance)
            (rat (fst (ρ ₊／₊ B)))
            (positiveRationalNonnegative (ρ ₊／₊ B))
            input-bound))
    where
    rational-product-path :
      rat (fst (ρ ₊／₊ B))
          · (rat (fst B) · coordinate-distance)
        ≡
      rat (fst ρ) · coordinate-distance
    rational-product-path =
      sym
        (mulAssoc
          (rat (fst (ρ ₊／₊ B)))
          (rat (fst B))
          coordinate-distance)
      ∙ cong
          (_· coordinate-distance)
          (mulComm
              (rat (fst (ρ ₊／₊ B)))
              (rat (fst B))
          ∙ mul-rat
              (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat (·／ B ρ))

  chainTotalErrorBound :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' : A → ℝ)
      (outer outer' : ℝ → ℝ)
      (x y : A) C G ε →
    absℝ (outer' (inner x)) ≤ℝ rat (fst G) →
    absℝ (inner y - inner x)
      ≤ℝ
    rat (fst C)
      · absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          (λ value → value) outer outer'
          (inner x) (inner y))
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ C))
      · absℝ (inner y - inner x) →
    absℝ
        (derivativeErrorAlong
          coordinate inner inner' x y)
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ G))
      · absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          coordinate
          (λ point → outer (inner point))
          (λ point →
            outer' (inner point) · inner' point)
          x y)
      ≤ℝ
    rat (fst ε)
      · absℝ (coordinate y - coordinate x)
  chainTotalErrorBound
    coordinate inner inner' outer outer'
    x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          absℝ error
            ≤ℝ rat (fst ε) · coordinate-distance)
        (sym
          (chainDerivativeErrorPath
            coordinate inner inner' outer outer' x y))
        (≤ℝ-trans
          (absℝ
            (outer-error
              + outer' (inner x) · inner-error))
          (absℝ outer-error
            + absℝ (outer' (inner x) · inner-error))
          (rat (fst ε) · coordinate-distance)
          (absTriangle
            outer-error
            (outer' (inner x) · inner-error))
          (subst
            ((absℝ outer-error
              + absℝ
                  (outer' (inner x) · inner-error)) ≤ℝ_)
            half-sum-path
            (≤ℝ-add
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
    coordinate-distance =
      absℝ (coordinate y - coordinate x)

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        (λ value → value) outer outer'
        (inner x) (inner y)

    inner-error : ℝ
    inner-error =
      derivativeErrorAlong
        coordinate inner inner' x y

    half-sum-path :
      rat (fst (ε /2₊)) · coordinate-distance
          + rat (fst (ε /2₊)) · coordinate-distance
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
          (rat+rat
            (fst (ε /2₊))
            (fst (ε /2₊))
          ∙ cong rat
              (1/2∈ℚ./2+/2≡id (fst ε)))

  chainThroughDerivativeErrorPath :
    ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
      (coordinate : A → ℝ)
      (map : A → B)
      (target-coordinate : B → ℝ)
      (inner' : A → ℝ)
      (outer outer' : B → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (outer ∘ map)
        (λ point → outer' (map point) · inner' point)
        x y
      ≡
    derivativeErrorAlong
        target-coordinate outer outer'
        (map x) (map y)
      + outer' (map x)
          · derivativeErrorAlong
              coordinate
              (target-coordinate ∘ map)
              inner' x y
  chainThroughDerivativeErrorPath
    coordinate map target-coordinate inner'
    outer outer' x y =
      cong
        (λ value → outer-difference - value)
        (mulAssoc
          (outer' (map x))
          (inner' x)
          displacement)
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' (map x) · inner-difference)
          (outer' (map x)
            · (inner' x · displacement)))
    ∙ cong
        (outer-error +_)
        (sym
          (ℝRing.·DistR-
            (outer' (map x))
            inner-difference
            (inner' x · displacement)))
    where
    displacement : ℝ
    displacement =
      coordinate y - coordinate x

    inner-difference : ℝ
    inner-difference =
      target-coordinate (map y)
        - target-coordinate (map x)

    outer-difference : ℝ
    outer-difference =
      outer (map y) - outer (map x)

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        target-coordinate outer outer'
        (map x) (map y)

  chainThroughTotalErrorBound :
    ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
      (coordinate : A → ℝ)
      (map : A → B)
      (target-coordinate : B → ℝ)
      (inner' : A → ℝ)
      (outer outer' : B → ℝ)
      (x y : A) C G ε →
    absℝ (outer' (map x)) ≤ℝ rat (fst G) →
    absℝ
        (target-coordinate (map y)
          - target-coordinate (map x))
      ≤ℝ
    rat (fst C)
      · absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          target-coordinate outer outer'
          (map x) (map y))
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ C))
      · absℝ
          (target-coordinate (map y)
            - target-coordinate (map x)) →
    absℝ
        (derivativeErrorAlong
          coordinate
          (target-coordinate ∘ map)
          inner' x y)
      ≤ℝ
    rat (fst ((ε /2₊) ₊／₊ G))
      · absℝ (coordinate y - coordinate x) →
    absℝ
        (derivativeErrorAlong
          coordinate
          (outer ∘ map)
          (λ point →
            outer' (map point) · inner' point)
          x y)
      ≤ℝ
    rat (fst ε)
      · absℝ (coordinate y - coordinate x)
  chainThroughTotalErrorBound
    coordinate map target-coordinate inner'
    outer outer' x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          absℝ error
            ≤ℝ rat (fst ε) · coordinate-distance)
        (sym
          (chainThroughDerivativeErrorPath
            coordinate map target-coordinate inner'
            outer outer' x y))
        (≤ℝ-trans
          (absℝ
            (outer-error
              + outer' (map x) · inner-error))
          (absℝ outer-error
            + absℝ (outer' (map x) · inner-error))
          (rat (fst ε) · coordinate-distance)
          (absTriangle
            outer-error
            (outer' (map x) · inner-error))
          (subst
            ((absℝ outer-error
              + absℝ
                  (outer' (map x) · inner-error)) ≤ℝ_)
            half-sum-path
            (≤ℝ-add
              (absℝ outer-error)
              (rat (fst (ε /2₊)) · coordinate-distance)
              (absℝ (outer' (map x) · inner-error))
              (rat (fst (ε /2₊)) · coordinate-distance)
              (boundedErrorThroughLinearInput
                outer-error inner-distance
                coordinate-distance C (ε /2₊)
                outer-error-bound inner-linear-bound)
              (boundedErrorProduct
                (outer' (map x)) inner-error
                coordinate-distance G (ε /2₊)
                outer'-bound inner-error-bound))))
    where
    coordinate-distance : ℝ
    coordinate-distance =
      absℝ (coordinate y - coordinate x)

    inner-distance : ℝ
    inner-distance =
      absℝ
        (target-coordinate (map y)
          - target-coordinate (map x))

    outer-error : ℝ
    outer-error =
      derivativeErrorAlong
        target-coordinate outer outer'
        (map x) (map y)

    inner-error : ℝ
    inner-error =
      derivativeErrorAlong
        coordinate
        (target-coordinate ∘ map)
        inner' x y

    half-sum-path :
      rat (fst (ε /2₊)) · coordinate-distance
          + rat (fst (ε /2₊)) · coordinate-distance
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
          (rat+rat
            (fst (ε /2₊))
            (fst (ε /2₊))
          ∙ cong rat
              (1/2∈ℚ./2+/2≡id (fst ε)))

-- A chain rule through an arbitrary intermediate premetric space.  The
-- intermediate map is continuous as a map of premetric spaces, while its
-- real coordinate is differentiable along the source coordinate.
chainHasDerivativeAlongThrough :
  ∀ {ℓA ℓA' ℓB ℓB'}
    {A : Type ℓA} {B : Type ℓB}
    (source : PremetricStr ℓA' A)
    (target : PremetricStr ℓB' B)
    (coordinate : A → ℝ)
    (map : A → B)
    (target-coordinate : B → ℝ)
    (inner' : A → ℝ)
    (outer outer' : B → ℝ) →
  isContinuous source coordinate
    (snd ℝPremetricSpace) →
  isContinuous source map target →
  IsDerivativeAlong
    source coordinate
    (target-coordinate ∘ map) inner' →
  IsDerivativeAlong
    target target-coordinate outer outer' →
  IsDerivativeAlong
    source coordinate
    (outer ∘ map)
    (λ point → outer' (map point) · inner' point)
chainHasDerivativeAlongThrough
  source target coordinate map target-coordinate inner'
  outer outer' coordinate-continuous map-continuous
  inner-derivative outer-derivative x ε = do
    (n , inner'-strict-bound) ←
      ∃naturalAbsBound (inner' x)
    (m , outer'-strict-bound) ←
      ∃naturalAbsBound (outer' (map x))
    let
      B : ℚ₊
      B = naturalBound n

      C : ℚ₊
      C = 1 +₊ B

      G : ℚ₊
      G = naturalBound m

      inner'-bound :
        absℝ (inner' x) ≤ℝ rat (fst B)
      inner'-bound =
        <ℝ-weaken
          (absℝ (inner' x))
          (rat (fst B)) inner'-strict-bound

      outer'-bound :
        absℝ (outer' (map x)) ≤ℝ rat (fst G)
      outer'-bound =
        <ℝ-weaken
          (absℝ (outer' (map x)))
          (rat (fst G)) outer'-strict-bound
    (δlinear , inner-linear-near) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate
        (target-coordinate ∘ map) inner'
        inner-derivative x B inner'-bound
    (δinner , inner-error-near) ←
      inner-derivative x ((ε /2₊) ₊／₊ G)
    (δouter , outer-error-near) ←
      outer-derivative
        (map x) ((ε /2₊) ₊／₊ C)
    (δcomposition , map-close-near) ←
      map-continuous x .IsContinuousAt.pres≈ δouter
    let
      δ : ℚ₊
      δ =
        min₊ δlinear
          (min₊ δinner δcomposition)
    return
      ( δ
      , λ y x∼δy →
          chainThroughTotalErrorBound
            coordinate map target-coordinate inner'
            outer outer' x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear
                  (min₊ δinner δcomposition))
                x∼δy))
            (outer-error-near (map y)
              (map-close-near y
                (PremetricStr.isMonotone≈≤
                  source x y δ δcomposition
                  (ℚ.isTrans≤
                    (fst δ)
                    (fst (min₊ δinner δcomposition))
                    (fst δcomposition)
                    (min₊≤R δlinear
                      (min₊ δinner δcomposition))
                    (min₊≤R δinner δcomposition))
                  x∼δy)))
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
                x∼δy))
      )

chainHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' : A → ℝ)
    (outer outer' : ℝ → ℝ) →
  isContinuous
    source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate inner inner' →
  IsDerivative outer outer' →
  IsDerivativeAlong
    source coordinate
    (λ point → outer (inner point))
    (λ point → outer' (inner point) · inner' point)
chainHasDerivativeAlong
  source coordinate inner inner' outer outer'
  coordinate-continuous inner-derivative outer-derivative
  x ε = do
    (n , inner'-strict-bound) ←
      ∃naturalAbsBound (inner' x)
    (m , outer'-strict-bound) ←
      ∃naturalAbsBound (outer' (inner x))
    let
      B : ℚ₊
      B = naturalBound n

      C : ℚ₊
      C = 1 +₊ B

      G : ℚ₊
      G = naturalBound m

      inner'-bound :
        absℝ (inner' x) ≤ℝ rat (fst B)
      inner'-bound =
        <ℝ-weaken
          (absℝ (inner' x))
          (rat (fst B))
          inner'-strict-bound

      outer'-bound :
        absℝ (outer' (inner x)) ≤ℝ rat (fst G)
      outer'-bound =
        <ℝ-weaken
          (absℝ (outer' (inner x)))
          (rat (fst G))
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
      δ =
        min₊ δlinear
          (min₊ δinner δcomposition)
    return
      ( δ
      , λ y x∼δy →
          chainTotalErrorBound
            coordinate inner inner' outer outer'
            x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear
                  (min₊ δinner δcomposition))
                x∼δy))
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
                  x∼δy)))
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
                x∼δy))
      )

chainHasDerivative :
  ∀ inner inner' outer outer' →
  IsDerivative inner inner' →
  IsDerivative outer outer' →
  IsDerivative
    (λ x → outer (inner x))
    (λ x → outer' (inner x) · inner' x)
chainHasDerivative inner inner' outer outer' =
  chainHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    inner inner' outer outer'
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
