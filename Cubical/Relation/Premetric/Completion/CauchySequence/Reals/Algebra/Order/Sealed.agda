module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


-- Frequently composed bridges between the completion's strict, non-strict,
-- and difference orders.  Sealing them keeps later analytic inequalities
-- modular without changing the underlying constructive witnesses.
opaque
  <ℝ-weaken-sealed : ∀ x y → x <ℝ y → x ≤ℝ y
  <ℝ-weaken-sealed = <ℝ-weaken


  ≤→zero≤difference-sealed : ∀ x y →
    x ≤ℝ y → zeroℝ ≤ℝ (y Group.- x)
  ≤→zero≤difference-sealed = ≤→zero≤difference


  strictlyPositiveDifference≪-sealed : ∀ x y →
    x <ℝ y → zeroℝ <ℝ (y Group.- x)
  strictlyPositiveDifference≪-sealed = strictlyPositiveDifference≪
