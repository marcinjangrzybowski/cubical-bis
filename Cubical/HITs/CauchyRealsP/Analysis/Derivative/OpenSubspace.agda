module Cubical.HITs.CauchyRealsP.Analysis.Derivative.OpenSubspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

openSubspaceDerivativeAtWithExtension :
  ∀ (P : ℙ ℝ) →
  IsOpenPredicate (snd ℝPremetricSpace) P →
  (relative-function relative-derivative :
    fst (PremetricSubspace ℝPremetricSpace P) → ℝ) →
  (function : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace ℝPremetricSpace P))
    fst
    relative-function
    relative-derivative →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (x∈P : x ∈ P) →
  IsDerivativeAt
    function
    (relative-derivative (x , x∈P))
    x
openSubspaceDerivativeAtWithExtension
  P openP relative-function relative-derivative function
  relative-has-derivative agrees x x∈P ε = do
    (derivative-radius , relative-bound) ←
      relative-has-derivative centre ε
    (domain-radius , stays-in-domain) ←
      openP x x∈P
    return
      ( min₊ derivative-radius domain-radius
      , λ y x∼y →
          let
            derivative-close :
              x ∼[ derivative-radius ] y
            derivative-close =
              PremetricStr.isMonotone≈≤
                (snd ℝPremetricSpace)
                x y
                (min₊ derivative-radius domain-radius)
                derivative-radius
                (min₊≤L derivative-radius domain-radius)
                x∼y

            domain-close :
              x ∼[ domain-radius ] y
            domain-close =
              PremetricStr.isMonotone≈≤
                (snd ℝPremetricSpace)
                x y
                (min₊ derivative-radius domain-radius)
                domain-radius
                (min₊≤R derivative-radius domain-radius)
                x∼y

            point : fst (PremetricSubspace ℝPremetricSpace P)
            point = y , stays-in-domain y domain-close

            relative-error-bound :
              absℝ
                  (relative-function point
                    - relative-function centre
                    - relative-derivative centre · (y - x))
                ≤ℝ
              rat (fst ε) · absℝ (y - x)
            relative-error-bound =
              relative-bound point derivative-close

            error-path :
              function y - function x
                  - relative-derivative centre · (y - x)
                ≡
              relative-function point
                  - relative-function centre
                  - relative-derivative centre · (y - x)
            error-path =
              cong₂
                (λ value-at-y value-at-x →
                  value-at-y - value-at-x
                    - relative-derivative centre · (y - x))
                (agrees point)
                (agrees centre)
          in
          subst
            (λ error →
              absℝ error ≤ℝ
                rat (fst ε) · absℝ (y - x))
            (sym error-path)
            relative-error-bound
      )
  where
  centre : fst (PremetricSubspace ℝPremetricSpace P)
  centre = x , x∈P

openSubspaceDerivativeAt :
  ∀ (P : ℙ ℝ) →
  IsOpenPredicate (snd ℝPremetricSpace) P →
  (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace ℝPremetricSpace P))
    fst
    (function ∘ fst)
    (derivative ∘ fst) →
  ∀ x →
  (x∈P : x ∈ P) →
  IsDerivativeAt function (derivative x) x
openSubspaceDerivativeAt
  P openP function derivative relative-has-derivative x x∈P =
    openSubspaceDerivativeAtWithExtension
      P openP
      (function ∘ fst)
      (derivative ∘ fst)
      function
      relative-has-derivative
      (λ _ → refl)
      x x∈P

-- The derivative may live on a larger, not necessarily open, subspace.  It
-- is enough to exhibit an open neighbourhood of the selected point which is
-- contained in that subspace.  This is the form used by closed intervals and
-- other domains with boundary.
subspaceDerivativeAtWithOpenNeighbourhoodAndExtension :
  ∀ (P Q : ℙ ℝ) →
  IsOpenPredicate (snd ℝPremetricSpace) Q →
  (Q⊆P : Q ⊆ P) →
  (relative-function relative-derivative :
    fst (PremetricSubspace ℝPremetricSpace P) → ℝ) →
  (function : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace ℝPremetricSpace P))
    fst
    relative-function
    relative-derivative →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (x∈Q : x ∈ Q) →
  IsDerivativeAt
    function
    (relative-derivative (x , Q⊆P x x∈Q))
    x
subspaceDerivativeAtWithOpenNeighbourhoodAndExtension
  P Q openQ Q⊆P relative-function relative-derivative function
  relative-has-derivative agrees x x∈Q =
    openSubspaceDerivativeAtWithExtension
      Q openQ
      (relative-function ∘ neighbourhood-inclusion)
      (relative-derivative ∘ neighbourhood-inclusion)
      function
      relative-has-derivative-on-neighbourhood
      (agrees ∘ neighbourhood-inclusion)
      x x∈Q
  where
  neighbourhood-inclusion :
    fst (PremetricSubspace ℝPremetricSpace Q) →
    fst (PremetricSubspace ℝPremetricSpace P)
  neighbourhood-inclusion point =
    fst point , Q⊆P (fst point) (snd point)

  neighbourhood-inclusion-is-continuous :
    isContinuous
      (snd (PremetricSubspace ℝPremetricSpace Q))
      neighbourhood-inclusion
      (snd (PremetricSubspace ℝPremetricSpace P))
  neighbourhood-inclusion-is-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( ε
        , λ _ point∼other → point∼other
        )

  relative-has-derivative-on-neighbourhood :
    IsDerivativeAlong
      (snd (PremetricSubspace ℝPremetricSpace Q))
      fst
      (relative-function ∘ neighbourhood-inclusion)
      (relative-derivative ∘ neighbourhood-inclusion)
  relative-has-derivative-on-neighbourhood =
    pullbackHasDerivativeAlong
      (snd (PremetricSubspace ℝPremetricSpace Q))
      (snd (PremetricSubspace ℝPremetricSpace P))
      fst relative-function relative-derivative
      neighbourhood-inclusion
      neighbourhood-inclusion-is-continuous
      relative-has-derivative

subspaceDerivativeAtWithOpenNeighbourhood :
  ∀ (P Q : ℙ ℝ) →
  IsOpenPredicate (snd ℝPremetricSpace) Q →
  Q ⊆ P →
  (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace ℝPremetricSpace P))
    fst
    (function ∘ fst)
    (derivative ∘ fst) →
  ∀ x →
  (x∈Q : x ∈ Q) →
  IsDerivativeAt function (derivative x) x
subspaceDerivativeAtWithOpenNeighbourhood
  P Q openQ Q⊆P function derivative
  relative-has-derivative x x∈Q =
    subspaceDerivativeAtWithOpenNeighbourhoodAndExtension
      P Q openQ Q⊆P
      (function ∘ fst)
      (derivative ∘ fst)
      function
      relative-has-derivative
      (λ _ → refl)
      x x∈Q
