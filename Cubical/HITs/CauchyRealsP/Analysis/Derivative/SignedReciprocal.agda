module Cubical.HITs.CauchyRealsP.Analysis.Derivative.SignedReciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Reciprocal

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

ApartRealPredicate : ℙ ℝ
ApartRealPredicate = 0＃ₚ

ApartReal : Type
ApartReal =
  Σ[ x ∈ ℝ ] x ∈ ApartRealPredicate

ApartRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
ApartRealPremetricSpace =
  PremetricSubspace
    ℝPremetricSpace ApartRealPredicate

apartRealCoordinate : ApartReal → ℝ
apartRealCoordinate = fst

apartRealCoordinateIsContinuous :
  isContinuous
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    (snd ℝPremetricSpace)
apartRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        ℝPremetricSpace ApartRealPredicate))

apartRealReciprocal : ApartReal → ℝ
apartRealReciprocal point =
  inverseℝ (fst point) (snd point)

apartRealReciprocalDerivative : ApartReal → ℝ
apartRealReciprocalDerivative point =
  - (apartRealReciprocal point
      · apartRealReciprocal point)

private
  RawReciprocalModulus :
    ApartReal → ℚ₊ → Type
  RawReciprocalModulus x ε =
    Σ[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_
          (snd ApartRealPremetricSpace) x δ y →
        absℝ
            (derivativeErrorAlong
              apartRealCoordinate
              apartRealReciprocal
              apartRealReciprocalDerivative
              x y)
          ≤ℝ
        rat (fst ε)
          · absℝ (fst y - fst x))

  ReciprocalModulus :
    ApartReal → ℚ₊ → Type
  ReciprocalModulus x ε =
    ∥ RawReciprocalModulus x ε ∥₁

  reciprocalAtPositiveGap :
    (x : ApartReal) →
    (0<x : 0 <ℝ fst x) →
    (ε : ℚ₊) →
    PositiveGap 0 (fst x) →
    ReciprocalModulus x ε
  reciprocalAtPositiveGap x 0<x ε w =
    PT.map convert-bound
      (positiveRealReciprocalHasDerivativeAlong
        x-positive ε)
    where
    x-positive : PositiveReal
    x-positive = fst x , 0<x

    half-width : ℚ₊
    half-width = width w /2₊

    convert-bound :
      Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd PositiveRealPremetricSpace)
            x-positive δ y →
          absℝ
              (derivativeErrorAlong
                positiveRealCoordinate
                positiveRealReciprocal
                positiveRealReciprocalDerivative
                x-positive y)
            ≤ℝ
          rat (fst ε)
            · absℝ (fst y - fst x))
      → RawReciprocalModulus x ε
    convert-bound (δ , positive-bound) =
      min₊ δ half-width
      , λ y x∼y →
          let
            x∼δy : fst x ∼[ δ ] fst y
            x∼δy =
              PremetricStr.isMonotone≈≤
                (snd ApartRealPremetricSpace)
                x y (min₊ δ half-width) δ
                (min₊≤L δ half-width) x∼y

            x∼halfy : fst x ∼[ half-width ] fst y
            x∼halfy =
              PremetricStr.isMonotone≈≤
                (snd ApartRealPremetricSpace)
                x y (min₊ δ half-width) half-width
                (min₊≤R δ half-width) x∼y

            y-positive-proof : 0 <ℝ fst y
            y-positive-proof =
              positiveGapHalfNeighbourPositive
                (fst x) (fst y) w x∼halfy

            y-positive : PositiveReal
            y-positive =
              fst y , y-positive-proof

            positive-error-bound =
              positive-bound y-positive x∼δy

            function-x-path :
              positiveRealReciprocal x-positive
                ≡ apartRealReciprocal x
            function-x-path =
              inverseℝProofIrrelevant
                (fst x) (inl 0<x) (snd x)

            function-y-path :
              positiveRealReciprocal y-positive
                ≡ apartRealReciprocal y
            function-y-path =
              inverseℝProofIrrelevant
                (fst y) (inl y-positive-proof) (snd y)

            derivative-x-path :
              positiveRealReciprocalDerivative x-positive
                ≡ apartRealReciprocalDerivative x
            derivative-x-path =
              cong (-_)
                (cong₂ _·_
                  function-x-path function-x-path)

            error-path :
              derivativeErrorAlong
                  apartRealCoordinate
                  apartRealReciprocal
                  apartRealReciprocalDerivative
                  x y
                ≡
              derivativeErrorAlong
                  positiveRealCoordinate
                  positiveRealReciprocal
                  positiveRealReciprocalDerivative
                  x-positive y-positive
            error-path =
              cong₂ _-_
                (cong₂ _-_
                  (sym function-y-path)
                  (sym function-x-path))
                (cong
                  (_· (fst y - fst x))
                  (sym derivative-x-path))
          in
          subst
            (λ error →
              absℝ error
                ≤ℝ
              rat (fst ε)
                · absℝ (fst y - fst x))
            (sym error-path)
            positive-error-bound

  reciprocalAtNegativeGap :
    (x : ApartReal) →
    (x<0 : fst x <ℝ 0) →
    (ε : ℚ₊) →
    PositiveGap 0 (- fst x) →
    ReciprocalModulus x ε
  reciprocalAtNegativeGap x x<0 ε w =
    PT.map convert-bound
      (negativeRealReciprocalHasDerivativeAlong
        x-negative ε)
    where
    x-negative : NegativeReal
    x-negative = fst x , x<0

    half-width : ℚ₊
    half-width = width w /2₊

    convert-bound :
      Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd NegativeRealPremetricSpace)
            x-negative δ y →
          absℝ
              (derivativeErrorAlong
                negativeRealCoordinate
                negativeRealReciprocal
                negativeRealReciprocalDerivative
                x-negative y)
            ≤ℝ
          rat (fst ε)
            · absℝ (fst y - fst x))
      → RawReciprocalModulus x ε
    convert-bound (δ , negative-bound) =
      min₊ δ half-width
      , λ y x∼y →
          let
            x∼δy : fst x ∼[ δ ] fst y
            x∼δy =
              PremetricStr.isMonotone≈≤
                (snd ApartRealPremetricSpace)
                x y (min₊ δ half-width) δ
                (min₊≤L δ half-width) x∼y

            x∼halfy : fst x ∼[ half-width ] fst y
            x∼halfy =
              PremetricStr.isMonotone≈≤
                (snd ApartRealPremetricSpace)
                x y (min₊ δ half-width) half-width
                (min₊≤R δ half-width) x∼y

            negx∼negy :
              (- fst x) ∼[ half-width ] (- fst y)
            negx∼negy =
              negPres∼
                (fst x) (fst y) half-width x∼halfy

            y-negative-proof : fst y <ℝ 0
            y-negative-proof =
              positiveNegationNegative
                (positiveGapHalfNeighbourPositive
                  (- fst x) (- fst y) w negx∼negy)

            y-negative : NegativeReal
            y-negative =
              fst y , y-negative-proof

            negative-error-bound =
              negative-bound y-negative x∼δy

            function-x-path :
              negativeRealReciprocal x-negative
                ≡ apartRealReciprocal x
            function-x-path =
              negativeRealReciprocal≡inverseℝ x-negative
              ∙ inverseℝProofIrrelevant
                  (fst x) (inr x<0) (snd x)

            function-y-path :
              negativeRealReciprocal y-negative
                ≡ apartRealReciprocal y
            function-y-path =
              negativeRealReciprocal≡inverseℝ y-negative
              ∙ inverseℝProofIrrelevant
                  (fst y) (inr y-negative-proof) (snd y)

            derivative-x-path :
              negativeRealReciprocalDerivative x-negative
                ≡ apartRealReciprocalDerivative x
            derivative-x-path =
              cong (-_)
                (cong₂ _·_
                  function-x-path function-x-path)

            error-path :
              derivativeErrorAlong
                  apartRealCoordinate
                  apartRealReciprocal
                  apartRealReciprocalDerivative
                  x y
                ≡
              derivativeErrorAlong
                  negativeRealCoordinate
                  negativeRealReciprocal
                  negativeRealReciprocalDerivative
                  x-negative y-negative
            error-path =
              cong₂ _-_
                (cong₂ _-_
                  (sym function-y-path)
                  (sym function-x-path))
                (cong
                  (_· (fst y - fst x))
                  (sym derivative-x-path))
          in
          subst
            (λ error →
              absℝ error
                ≤ℝ
              rat (fst ε)
                · absℝ (fst y - fst x))
            (sym error-path)
            negative-error-bound

apartRealReciprocalHasDerivativeAlong :
  IsDerivativeAlong
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    apartRealReciprocal
    apartRealReciprocalDerivative
apartRealReciprocalHasDerivativeAlong x ε =
  ⊎.rec
    (λ 0<x →
      PT.rec squash₁
        (reciprocalAtPositiveGap x 0<x ε) 0<x)
    (λ x<0 →
      PT.rec squash₁
        (reciprocalAtNegativeGap x x<0 ε)
        (negativeNegationPositive x<0))
    (snd x)

apartRealReciprocalIsContinuous :
  isContinuous
    (snd ApartRealPremetricSpace)
    apartRealReciprocal
    (snd ℝPremetricSpace)
apartRealReciprocalIsContinuous =
  derivativeAlongIsContinuous
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    apartRealReciprocal
    apartRealReciprocalDerivative
    apartRealCoordinateIsContinuous
    apartRealReciprocalHasDerivativeAlong
