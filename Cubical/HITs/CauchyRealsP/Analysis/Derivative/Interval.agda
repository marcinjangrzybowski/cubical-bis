module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.OpenSubspace
open import
  Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval
open import
  Cubical.HITs.CauchyRealsP.Analysis.Metric.IntervalExtension

closedIntervalDerivativeAtInteriorWithExtension :
  ∀ a b
    (relative-function relative-derivative :
      ClosedInterval a b → ℝ)
    (function : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst
    relative-function
    relative-derivative →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (a<x : a <ℝ x) →
  (x<b : x <ℝ b) →
  IsDerivativeAt
    function
    (relative-derivative
      ( x
      , <ℝ-weaken a x a<x
      , <ℝ-weaken x b x<b
      ))
    x
closedIntervalDerivativeAtInteriorWithExtension
  a b relative-function relative-derivative function
  relative-has-derivative agrees x a<x x<b =
    subspaceDerivativeAtWithOpenNeighbourhoodAndExtension
      (ClosedIntervalPredicate a b)
      (OpenIntervalPredicate a b)
      (openIntervalIsOpen a b)
      (openInterval⊆closedInterval a b)
      relative-function
      relative-derivative
      function
      relative-has-derivative
      agrees
      x (a<x , x<b)

closedIntervalDerivativeAtInterior :
  ∀ a b (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst
    (function ∘ fst)
    (derivative ∘ fst) →
  ∀ x →
  a <ℝ x →
  x <ℝ b →
  IsDerivativeAt function (derivative x) x
closedIntervalDerivativeAtInterior
  a b function derivative relative-has-derivative x a<x x<b =
    subspaceDerivativeAtWithOpenNeighbourhood
      (ClosedIntervalPredicate a b)
      (OpenIntervalPredicate a b)
      (openIntervalIsOpen a b)
      (openInterval⊆closedInterval a b)
      function derivative
      relative-has-derivative
      x (a<x , x<b)

-- The clamp extension supplies the ambient function canonically.  It may
-- have corners at the endpoints, but at a strict interior point it agrees on
-- a whole neighbourhood with the relative function, which is exactly what
-- the local derivative argument needs.
closedIntervalClampExtensionDerivativeAtInterior :
  ∀ a b →
  (a≤b : a ≤ℝ b) →
  (relative-function relative-derivative :
    ClosedInterval a b → ℝ) →
  IsDerivativeAlong
    (snd (ClosedIntervalPremetricSpace a b))
    fst
    relative-function
    relative-derivative →
  ∀ x →
  (a<x : a <ℝ x) →
  (x<b : x <ℝ b) →
  IsDerivativeAt
    (extendClosedInterval a b a≤b relative-function)
    (relative-derivative
      ( x
      , <ℝ-weaken a x a<x
      , <ℝ-weaken x b x<b
      ))
    x
closedIntervalClampExtensionDerivativeAtInterior
  a b a≤b relative-function relative-derivative
  relative-has-derivative x a<x x<b =
    closedIntervalDerivativeAtInteriorWithExtension
      a b
      relative-function
      relative-derivative
      (extendClosedInterval a b a≤b relative-function)
      relative-has-derivative
      (extendClosedIntervalAgrees a b a≤b relative-function)
      x a<x x<b
