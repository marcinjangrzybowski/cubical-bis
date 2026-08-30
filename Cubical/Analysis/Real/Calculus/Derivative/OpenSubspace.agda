module Cubical.Analysis.Real.Calculus.Derivative.OpenSubspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; min₊; min₊≤L; min₊≤R)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Base


-- Ambient differentiability restricts along every predicate inclusion; no
-- openness hypothesis is needed in this direction.

restrictDerivativeToSubspace :
  ∀ (P : ℙ ℝ) (function derivative : ℝ → ℝ) →
  IsDerivative function derivative →
  IsDerivativeAlong
    (PremetricSubspace ℝPremetricSpace P .snd)
    fst
    (function ∘ fst)
    (derivative ∘ fst)
restrictDerivativeToSubspace P function derivative has-derivative =
  pullbackHasDerivativeAlong
    (PremetricSubspace ℝPremetricSpace P .snd)
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    function
    derivative
    fst
    (snd (NE→C (subspaceInclusionNE ℝPremetricSpace P)))
    has-derivative


-- Conversely, openness supplies an ambient neighbourhood on which the
-- relative derivative estimate can be used.  The extension only has to
-- agree pointwise with the relative function; no global choice of a domain
-- radius is made.

openSubspaceDerivativeAtWithExtension :
  ∀ (P : ℙ ℝ) →
  IsOpenPredicate (ℝPremetricSpace .snd) P →
  (relative-function relative-derivative :
    fst (PremetricSubspace ℝPremetricSpace P) → ℝ) →
  (function : ℝ → ℝ) →
  IsDerivativeAlong
    (PremetricSubspace ℝPremetricSpace P .snd)
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
                (ℝPremetricSpace .snd)
                x y
                (min₊ derivative-radius domain-radius)
                derivative-radius
                (min₊≤L derivative-radius domain-radius)
                x∼y

            domain-close :
              x ∼[ domain-radius ] y
            domain-close =
              PremetricStr.isMonotone≈≤
                (ℝPremetricSpace .snd)
                x y
                (min₊ derivative-radius domain-radius)
                domain-radius
                (min₊≤R derivative-radius domain-radius)
                x∼y

            point : fst (PremetricSubspace ℝPremetricSpace P)
            point = y , stays-in-domain y domain-close

            relative-error-bound :
              absℝ
                  ((relative-function point
                      - relative-function centre)
                    -
                    (relative-derivative centre · (y - x)))
                ≤ℝ
              rat (fst ε) · absℝ (y - x)
            relative-error-bound =
              relative-bound point derivative-close

            error-path :
              ((function y - function x)
                  - (relative-derivative centre · (y - x)))
                ≡
              ((relative-function point - relative-function centre)
                  - (relative-derivative centre · (y - x)))
            error-path =
              cong₂
                (λ value-at-y value-at-x →
                  (value-at-y - value-at-x)
                    - (relative-derivative centre · (y - x)))
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
  IsOpenPredicate (ℝPremetricSpace .snd) P →
  (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (PremetricSubspace ℝPremetricSpace P .snd)
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
