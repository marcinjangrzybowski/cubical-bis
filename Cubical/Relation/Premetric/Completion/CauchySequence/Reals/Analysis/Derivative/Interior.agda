module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Interior where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius


-- A derivative proved uniformly on a closed radius is an ordinary derivative
-- at every strict interior point.  Openness supplies the smaller local
-- neighbourhood; no global selection of radii is involved.

closedAbsRadiusDerivativeAtInterior :
  ∀ radius
    (function derivative : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (λ point → function (fst point))
    (λ point → derivative (fst point)) →
  ∀ x →
  Abs.absℝ x <ℝ radius →
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


-- A function available only on the closed-radius subspace can determine an
-- ordinary derivative of any agreeing ambient extension at a strict interior
-- point.  The derivative itself needs no ambient extension.

closedAbsRadiusDerivativeAtInteriorWithExtension :
  ∀ radius
    (relative-function relative-derivative :
      ClosedAbsRadius radius → Real.ℝ)
    (function : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    relative-function
    relative-derivative →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (interior : Abs.absℝ x <ℝ radius) →
  IsDerivativeAt
    function
    (relative-derivative
      (x , <ℝ-weaken (Abs.absℝ x) radius interior))
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
