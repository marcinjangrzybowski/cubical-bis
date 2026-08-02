module Cubical.HITs.CauchyRealsP.Analysis.Metric.IntervalExtension where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open CategoryStructures

private
  variable
    ℓN ℓN' : Level

extendClosedInterval :
  ∀ {A : Type ℓN} a b →
  a ≤ℝ b →
  (ClosedInterval a b → A) →
  ℝ → A
extendClosedInterval a b a≤b function x =
  function (fst (clampIntervalRetractionNE a b a≤b) x)

extendClosedIntervalAgrees :
  ∀ {A : Type ℓN} a b →
  (a≤b : a ≤ℝ b) →
  (function : ClosedInterval a b → A) →
  ∀ point →
  extendClosedInterval a b a≤b function (fst point)
    ≡ function point
extendClosedIntervalAgrees a b a≤b function point =
  cong function
    (clampIntervalRetractionSection a b a≤b point)

extendClosedIntervalNE :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  NE[ ClosedIntervalPremetricSpace a b , target ] →
  NE[ ℝPremetricSpace , target ]
extendClosedIntervalNE target a b a≤b function =
  function ∘NE clampIntervalRetractionNE a b a≤b

extendClosedIntervalUC :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  UC[ ClosedIntervalPremetricSpace a b , target ] →
  UC[ ℝPremetricSpace , target ]
extendClosedIntervalUC target a b a≤b function =
  function ∘UC
    NE→UC (clampIntervalRetractionNE a b a≤b)

extendClosedIntervalC :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  a ≤ℝ b →
  C[ ClosedIntervalPremetricSpace a b , target ] →
  C[ ℝPremetricSpace , target ]
extendClosedIntervalC target a b a≤b function =
  function ∘C
    NE→C (clampIntervalRetractionNE a b a≤b)

extendClosedIntervalNEAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : NE[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalNE target a b a≤b function) (fst point)
    ≡ fst function point
extendClosedIntervalNEAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point

extendClosedIntervalUCAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : UC[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalUC target a b a≤b function) (fst point)
    ≡ fst function point
extendClosedIntervalUCAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point

extendClosedIntervalCAgrees :
  ∀ (target : PremetricSpace ℓN ℓN') a b →
  (a≤b : a ≤ℝ b) →
  (function : C[ ClosedIntervalPremetricSpace a b , target ]) →
  ∀ point →
  fst (extendClosedIntervalC target a b a≤b function) (fst point)
    ≡ fst function point
extendClosedIntervalCAgrees target a b a≤b function point =
  extendClosedIntervalAgrees a b a≤b (fst function) point
