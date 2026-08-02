module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  positiveRationalNonnegative :
    ∀ B → 0 ≤ℝ rat (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      0 (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  derivativeErrorReconstructsDifference :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate function derivative : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate function derivative x y
      + derivative x
          · (coordinate y - coordinate x)
      ≡
    function y - function x
  derivativeErrorReconstructsDifference
    coordinate function derivative x y =
      subAddCancel
        (function y - function x)
        (derivative x
          · (coordinate y - coordinate x))

-- A derivative with a selected bound on its value is locally Lipschitz in
-- the coordinate, with coefficient `1 + B`.  This estimate deliberately
-- remains relative to the coordinate; continuity in the source follows only
-- when the coordinate map is itself continuous.
derivativeAlongLocalLinearBoundAt :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ x B →
  absℝ (derivative x) ≤ℝ rat (fst B) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      PremetricStr._≈[_]_ source x δ y →
      absℝ (function y - function x)
        ≤ℝ
      rat (fst (1 +₊ B))
        · absℝ (coordinate y - coordinate x))
derivativeAlongLocalLinearBoundAt
  {A = A} source coordinate function derivative
  has-derivative x B derivative-bound = do
    (δ , error-bound) ← has-derivative x 1
    return
      ( δ
      , λ y x∼y →
          difference-bound y (error-bound y x∼y)
      )
  where
  distance : A → ℝ
  distance y =
    absℝ (coordinate y - coordinate x)

  coefficient-path :
    ∀ y →
    rat (fst (1 +₊ B)) · distance y
      ≡
    rat 1 · distance y
      + rat (fst B) · distance y
  coefficient-path y =
    cong
      (_· distance y)
      (sym
        (rat+rat
          1 (fst B)))
    ∙ mulDistL
        (rat 1)
        (rat (fst B))
        (distance y)

  linear-bound :
    ∀ y →
    absℝ
        (derivative x
          · (coordinate y - coordinate x))
      ≤ℝ
    rat (fst B) · distance y
  linear-bound y =
    subst
      (_≤ℝ rat (fst B) · distance y)
      (sym
        (absMul
          (derivative x)
          (coordinate y - coordinate x)))
      (mulMonoR≤
        (absℝ (derivative x))
        (rat (fst B))
        (distance y)
        (absNonnegative
          (coordinate y - coordinate x))
        derivative-bound)

  difference-bound :
    ∀ y →
    absℝ
        (derivativeErrorAlong
          coordinate function derivative x y)
      ≤ℝ
    rat 1 · distance y →
    absℝ (function y - function x)
      ≤ℝ
    rat (fst (1 +₊ B)) · distance y
  difference-bound y error-bound =
    subst
      (λ value →
        absℝ value
          ≤ℝ rat (fst (1 +₊ B)) · distance y)
      (derivativeErrorReconstructsDifference
        coordinate function derivative x y)
      (≤ℝ-trans
        (absℝ
          (derivativeErrorAlong
              coordinate function derivative x y
            + derivative x
                · (coordinate y - coordinate x)))
        (absℝ
            (derivativeErrorAlong
              coordinate function derivative x y)
          + absℝ
              (derivative x
                · (coordinate y - coordinate x)))
        (rat (fst (1 +₊ B)) · distance y)
        (absTriangle
          (derivativeErrorAlong
            coordinate function derivative x y)
          (derivative x
            · (coordinate y - coordinate x)))
        (subst
          ((absℝ
              (derivativeErrorAlong
                coordinate function derivative x y)
            + absℝ
                (derivative x
                  · (coordinate y - coordinate x))) ≤ℝ_)
          (sym (coefficient-path y))
          (≤ℝ-add
            (absℝ
              (derivativeErrorAlong
                coordinate function derivative x y))
            (rat 1 · distance y)
            (absℝ
              (derivative x
                · (coordinate y - coordinate x)))
            (rat (fst B) · distance y)
            error-bound
            (linear-bound y))))

derivativeAlongIsContinuousAtBound :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ)
    (x : A) B →
  absℝ (derivative x) ≤ℝ rat (fst B) →
  IsContinuousAt
    source coordinate (snd ℝPremetricSpace) x →
  IsDerivativeAlong source coordinate function derivative →
  IsContinuousAt
    source function (snd ℝPremetricSpace) x
derivativeAlongIsContinuousAtBound
  source coordinate function derivative x B
  derivative-bound coordinate-continuous has-derivative
  .IsContinuousAt.pres≈ ε = do
    (δlinear , linear-bound) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate function derivative
        has-derivative x B derivative-bound
    (δcoordinate , coordinate-close) ←
      coordinate-continuous .IsContinuousAt.pres≈
        (ε ₊／₊ (1 +₊ B))
    return
      ( min₊ δlinear δcoordinate
      , λ y x∼y →
          output-close y
            (linear-bound y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δlinear δcoordinate)
                δlinear
                (min₊≤L δlinear δcoordinate)
                x∼y))
            (coordinate-close y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δlinear δcoordinate)
                δcoordinate
                (min₊≤R δlinear δcoordinate)
                x∼y))
      )
  where
  C : ℚ₊
  C = 1 +₊ B

  output-close :
    ∀ y →
    absℝ (function y - function x)
      ≤ℝ
    rat (fst C)
      · absℝ (coordinate y - coordinate x) →
    coordinate x ∼[ ε ₊／₊ C ] coordinate y →
    function x ∼[ ε ] function y
  output-close y function-bound coordinate-near =
    absDifference<→closeness
      (function x) (function y) ε
      (subst
        (_<ℝ rat (fst ε))
        (absSubComm (function y) (function x))
        (≤<ℝ-trans
          (absℝ (function y - function x))
          (rat (fst C)
            · absℝ (coordinate y - coordinate x))
          (rat (fst ε))
          function-bound
          (subst
            ((rat (fst C)
              · absℝ
                  (coordinate y - coordinate x)) <ℝ_)
            (mul-rat
              (fst C) (fst (ε ₊／₊ C))
            ∙ cong rat (·／ C ε))
            (mulMonoL<
              (absℝ
                (coordinate y - coordinate x))
              (rat (fst (ε ₊／₊ C)))
              (rat (fst C))
              (<ℚ→<ℝ 0 (fst C) (snd C))
              (subst
                (_<ℝ rat (fst (ε ₊／₊ C)))
                (absSubComm
                  (coordinate x) (coordinate y))
                (closeness→absDifference<
                  (coordinate x) (coordinate y)
                  (ε ₊／₊ C) coordinate-near))))))

derivativeAlongIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  isContinuous source coordinate (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate function derivative →
  isContinuous source function (snd ℝPremetricSpace)
derivativeAlongIsContinuous
  source coordinate function derivative
  coordinate-continuous has-derivative x
  .IsContinuousAt.pres≈ ε = do
    (n , derivative-strict-bound) ←
      ∃naturalAbsBound (derivative x)
    derivativeAlongIsContinuousAtBound
        source coordinate function derivative x
        (naturalBound n)
        (<ℝ-weaken
          (absℝ (derivative x))
          (rat (fst (naturalBound n)))
          derivative-strict-bound)
        (coordinate-continuous x)
        has-derivative
      .IsContinuousAt.pres≈ ε

derivativeIsContinuous :
  ∀ function derivative →
  IsDerivative function derivative →
  isContinuous
    (snd ℝPremetricSpace) function
    (snd ℝPremetricSpace)
derivativeIsContinuous function derivative =
  derivativeAlongIsContinuous
    (snd ℝPremetricSpace)
    (idfun ℝ)
    function derivative
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
