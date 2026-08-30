module Cubical.Analysis.Real.Calculus.Derivative.Interior where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Domain.OpenRadius
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.OpenSubspace


-- A function defined on a closed radius determines the derivative of every
-- agreeing ambient extension at strict interior points.  The proof first
-- pulls the relative derivative back to the open-radius neighbourhood.

closedAbsRadiusDerivativeAtInteriorWithExtension :
  ∀ radius
    (relative-function relative-derivative :
      ClosedAbsRadius radius → ℝ)
    (function : ℝ → ℝ) →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
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
  openSubspaceDerivativeAtWithExtension
    (OpenAbsRadiusPredicate radius)
    (openAbsRadiusIsOpen radius)
    (relative-function ∘ open-to-closed)
    (relative-derivative ∘ open-to-closed)
    function
    relative-has-derivative-on-interior
    (agrees ∘ open-to-closed)
    x interior
  where
  open-to-closed :
    OpenAbsRadius radius → ClosedAbsRadius radius
  open-to-closed point =
    fst point
    , <ℝ-weaken (absℝ (fst point)) radius (snd point)

  open-to-closed-is-continuous :
    isContinuous
      (OpenAbsRadiusPremetricSpace radius .snd)
      open-to-closed
      (ClosedAbsRadiusPremetricSpace radius .snd)
  open-to-closed-is-continuous
    point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ point≈other → point≈other
      )

  relative-has-derivative-on-interior :
    IsDerivativeAlong
      (OpenAbsRadiusPremetricSpace radius .snd)
      fst
      (relative-function ∘ open-to-closed)
      (relative-derivative ∘ open-to-closed)
  relative-has-derivative-on-interior =
    pullbackHasDerivativeAlong
      (OpenAbsRadiusPremetricSpace radius .snd)
      (ClosedAbsRadiusPremetricSpace radius .snd)
      fst relative-function relative-derivative
      open-to-closed
      open-to-closed-is-continuous
      relative-has-derivative


closedAbsRadiusDerivativeAtInterior :
  ∀ radius
    (function derivative : ℝ → ℝ) →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (function ∘ fst)
    (derivative ∘ fst) →
  ∀ x →
  absℝ x <ℝ radius →
  IsDerivativeAt function (derivative x) x
closedAbsRadiusDerivativeAtInterior
  radius function derivative relative-has-derivative =
  closedAbsRadiusDerivativeAtInteriorWithExtension
    radius
    (function ∘ fst)
    (derivative ∘ fst)
    function
    relative-has-derivative
    (λ _ → refl)
