module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Interior where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.OpenSubspace
open import
  Cubical.HITs.CauchyRealsP.Analysis.Metric.Radius

closedAbsRadiusDerivativeAtInterior :
  ∀ radius
    (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (λ point → function (fst point))
    (λ point → derivative (fst point)) →
  ∀ x →
  absℝ x <ℝ radius →
  IsDerivativeAt function (derivative x) x
closedAbsRadiusDerivativeAtInterior
  radius function derivative
  relative-derivative x interior =
    subspaceDerivativeAtWithOpenNeighbourhood
      (ClosedAbsRadiusPredicate radius)
      (OpenAbsRadiusPredicate radius)
      (openAbsRadiusIsOpen radius)
      (openAbsRadius⊆closedAbsRadius radius)
      function derivative
      relative-derivative
      x interior

-- A function defined only on a closed-radius subspace can still determine an
-- ordinary derivative at a strict interior point, provided it agrees there
-- with an ambient real function.  No ambient extension of the derivative is
-- needed: its value at the selected subspace point is enough.
closedAbsRadiusDerivativeAtInteriorWithExtension :
  ∀ radius
    (relative-function relative-derivative :
      ClosedAbsRadius radius → ℝ)
    (function : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    relative-function
    relative-derivative →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (interior : absℝ x <ℝ radius) →
  IsDerivativeAt
    function
    (relative-derivative
      (x , <ℝ-weaken (absℝ x) radius interior))
    x
closedAbsRadiusDerivativeAtInteriorWithExtension
  radius relative-function relative-derivative function
  relative-has-derivative agrees x interior =
    subspaceDerivativeAtWithOpenNeighbourhoodAndExtension
      (ClosedAbsRadiusPredicate radius)
      (OpenAbsRadiusPredicate radius)
      (openAbsRadiusIsOpen radius)
      (openAbsRadius⊆closedAbsRadius radius)
      relative-function relative-derivative function
      relative-has-derivative agrees
      x interior
