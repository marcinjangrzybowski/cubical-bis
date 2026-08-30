module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.OpenSubspace
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Interval
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.IntervalExtension


closedIntervalDerivativeAtInteriorWithExtension :
  ∀ a b
    (relative-function relative-derivative :
      ClosedInterval a b → Real.ℝ)
    (function : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst relative-function relative-derivative →
  (∀ point → function (fst point) ≡ relative-function point) →
  ∀ x →
  (a<x : a <ℝ x) →
  (x<b : x <ℝ b) →
  IsDerivativeAt function
    (relative-derivative
      (x , <ℝ-weaken a x a<x , <ℝ-weaken x b x<b))
    x
closedIntervalDerivativeAtInteriorWithExtension
  a b relative-function relative-derivative function
  relative-has-derivative agrees x a<x x<b =
    subspaceDerivativeAtWithOpenNeighbourhoodAndExtension
      (ClosedIntervalPredicate a b)
      (OpenIntervalPredicate a b)
      (openIntervalIsOpen a b)
      (openInterval⊆closedInterval a b)
      relative-function relative-derivative function
      relative-has-derivative agrees
      x (a<x , x<b)


closedIntervalDerivativeAtInterior :
  ∀ a b (function derivative : Real.ℝ → Real.ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst (function ∘ fst) (derivative ∘ fst) →
  ∀ x → a <ℝ x → x <ℝ b →
  IsDerivativeAt function (derivative x) x
closedIntervalDerivativeAtInterior
  a b function derivative relative-has-derivative x a<x x<b =
    subspaceDerivativeAtWithOpenNeighbourhood
      (ClosedIntervalPredicate a b)
      (OpenIntervalPredicate a b)
      (openIntervalIsOpen a b)
      (openInterval⊆closedInterval a b)
      function derivative relative-has-derivative
      x (a<x , x<b)


-- The canonical clamp extension can have corners at the endpoints, but at
-- every strict interior point it agrees on an open neighbourhood with the
-- relative function.  Thus relative differentiability is enough there.

closedIntervalClampExtensionDerivativeAtInterior :
  ∀ a b →
  (a≤b : a ≤ℝ b) →
  (relative-function relative-derivative :
    ClosedInterval a b → Real.ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst relative-function relative-derivative →
  ∀ x →
  (a<x : a <ℝ x) →
  (x<b : x <ℝ b) →
  IsDerivativeAt
    (extendClosedInterval a b a≤b relative-function)
    (relative-derivative
      (x , <ℝ-weaken a x a<x , <ℝ-weaken x b x<b))
    x
closedIntervalClampExtensionDerivativeAtInterior
  a b a≤b relative-function relative-derivative
  relative-has-derivative x a<x x<b =
    closedIntervalDerivativeAtInteriorWithExtension
      a b relative-function relative-derivative
      (extendClosedInterval a b a≤b relative-function)
      relative-has-derivative
      (extendClosedIntervalAgrees a b a≤b relative-function)
      x a<x x<b
