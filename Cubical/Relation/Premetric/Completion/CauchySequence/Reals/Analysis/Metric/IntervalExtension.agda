module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.IntervalExtension where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Interval


private
  variable
    ℓN ℓN' : Level


-- Precomposition with the clamp gives a canonical total extension.  Unlike
-- an existence-only extension principle, this supplies a concrete function,
-- preservation of quantitative continuity, and an exact agreement rule.

extendClosedInterval :
  ∀ {A : Type ℓN} a b →
  a ≤ℝ b →
  (ClosedInterval a b → A) →
  Real.ℝ → A
extendClosedInterval a b a≤b function x =
  function (fst (canonicalClosedIntervalRetractionNE a b a≤b) x)


extendClosedIntervalAgrees :
  ∀ {A : Type ℓN} a b →
  (a≤b : a ≤ℝ b) →
  (function : ClosedInterval a b → A) → ∀ point →
  extendClosedInterval a b a≤b function (fst point) ≡ function point
extendClosedIntervalAgrees a b a≤b function point =
  cong function (canonicalClosedIntervalRetractionSection a b a≤b point)


extendClosedIntervalNE :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  NE[ ClosedIntervalPremetricSpace a b , target ] →
  NE[ Real.ℝPremetricSpace , target ]
extendClosedIntervalNE target a b a≤b function =
  function ∘NE canonicalClosedIntervalRetractionNE a b a≤b


extendClosedIntervalUC :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  UC[ ClosedIntervalPremetricSpace a b , target ] →
  UC[ Real.ℝPremetricSpace , target ]
extendClosedIntervalUC target a b a≤b function =
  function ∘UC NE→UC (canonicalClosedIntervalRetractionNE a b a≤b)


extendClosedIntervalC :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  C[ ClosedIntervalPremetricSpace a b , target ] →
  C[ Real.ℝPremetricSpace , target ]
extendClosedIntervalC target a b a≤b function =
  function ∘C NE→C (canonicalClosedIntervalRetractionNE a b a≤b)


extendClosedIntervalNEAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : NE[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalNE target a b a≤b function) (fst point) ≡
    fst function point
extendClosedIntervalNEAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point


extendClosedIntervalUCAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : UC[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalUC target a b a≤b function) (fst point) ≡
    fst function point
extendClosedIntervalUCAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point


extendClosedIntervalCAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : C[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalC target a b a≤b function) (fst point) ≡
    fst function point
extendClosedIntervalCAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point
