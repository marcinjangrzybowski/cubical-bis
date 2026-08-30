module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


-- A derivative on an open subspace determines the ordinary derivative of
-- any ambient extension.  Both neighbourhood witnesses remain under
-- propositional truncation and are combined only inside the derivative
-- proposition.

openSubspaceDerivativeAtWithExtension :
  ∀ (P : ℙ Real.ℝ) →
  IsOpenPredicate (snd Real.ℝPremetricSpace) P →
  (relative-function relative-derivative :
    fst (PremetricSubspace Real.ℝPremetricSpace P) → Real.ℝ) →
  (function : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace Real.ℝPremetricSpace P))
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
      , λ y x≈y →
          let
            derivative-close :
              x Real.Base.≈ᶜ[ derivative-radius ] y
            derivative-close =
              PremetricStr.isMonotone≈≤
                (snd Real.ℝPremetricSpace)
                x y
                (min₊ derivative-radius domain-radius)
                derivative-radius
                (min₊≤L derivative-radius domain-radius)
                x≈y

            domain-close :
              x Real.Base.≈ᶜ[ domain-radius ] y
            domain-close =
              PremetricStr.isMonotone≈≤
                (snd Real.ℝPremetricSpace)
                x y
                (min₊ derivative-radius domain-radius)
                domain-radius
                (min₊≤R derivative-radius domain-radius)
                x≈y

            point : fst (PremetricSubspace Real.ℝPremetricSpace P)
            point = y , stays-in-domain y domain-close

            relative-error-bound :
              Abs.absℝ
                  ((relative-function point
                      Group.- relative-function centre)
                    Group.-
                    (relative-derivative centre Mul.·
                      (y Group.- x)))
                ≤ℝ
              Real.ιℚ (fst ε) Mul.· Abs.absℝ (y Group.- x)
            relative-error-bound =
              relative-bound point derivative-close

            error-path :
              ((function y Group.- function x) Group.-
                  (relative-derivative centre Mul.· (y Group.- x)))
                ≡
              ((relative-function point
                  Group.- relative-function centre) Group.-
                  (relative-derivative centre Mul.· (y Group.- x)))
            error-path =
              cong₂
                (λ value-at-y value-at-x →
                  (value-at-y Group.- value-at-x) Group.-
                    (relative-derivative centre Mul.· (y Group.- x)))
                (agrees point)
                (agrees centre)
          in
          subst
            (λ error →
              Abs.absℝ error ≤ℝ
                Real.ιℚ (fst ε) Mul.· Abs.absℝ (y Group.- x))
            (sym error-path)
            relative-error-bound
      )
  where
  centre : fst (PremetricSubspace Real.ℝPremetricSpace P)
  centre = x , x∈P


openSubspaceDerivativeAt :
  ∀ (P : ℙ Real.ℝ) →
  IsOpenPredicate (snd Real.ℝPremetricSpace) P →
  (function derivative : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace Real.ℝPremetricSpace P))
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
-- suffices to exhibit an open neighbourhood of the selected point contained
-- in that subspace.  This is the form needed for closed-radius domains.

subspaceDerivativeAtWithOpenNeighbourhoodAndExtension :
  ∀ (P Q : ℙ Real.ℝ) →
  IsOpenPredicate (snd Real.ℝPremetricSpace) Q →
  (Q⊆P : Q ⊆ P) →
  (relative-function relative-derivative :
    fst (PremetricSubspace Real.ℝPremetricSpace P) → Real.ℝ) →
  (function : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace Real.ℝPremetricSpace P))
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
    fst (PremetricSubspace Real.ℝPremetricSpace Q) →
    fst (PremetricSubspace Real.ℝPremetricSpace P)
  neighbourhood-inclusion point =
    fst point , Q⊆P (fst point) (snd point)

  neighbourhood-inclusion-is-continuous :
    isContinuous
      (snd (PremetricSubspace Real.ℝPremetricSpace Q))
      neighbourhood-inclusion
      (snd (PremetricSubspace Real.ℝPremetricSpace P))
  neighbourhood-inclusion-is-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( ε
        , λ _ point≈other → point≈other
        )

  relative-has-derivative-on-neighbourhood :
    IsDerivativeAlong
      (snd (PremetricSubspace Real.ℝPremetricSpace Q))
      fst
      (relative-function ∘ neighbourhood-inclusion)
      (relative-derivative ∘ neighbourhood-inclusion)
  relative-has-derivative-on-neighbourhood =
    pullbackHasDerivativeAlong
      (snd (PremetricSubspace Real.ℝPremetricSpace Q))
      (snd (PremetricSubspace Real.ℝPremetricSpace P))
      fst relative-function relative-derivative
      neighbourhood-inclusion
      neighbourhood-inclusion-is-continuous
      relative-has-derivative


subspaceDerivativeAtWithOpenNeighbourhood :
  ∀ (P Q : ℙ Real.ℝ) →
  IsOpenPredicate (snd Real.ℝPremetricSpace) Q →
  Q ⊆ P →
  (function derivative : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (PremetricSubspace Real.ℝPremetricSpace P))
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
