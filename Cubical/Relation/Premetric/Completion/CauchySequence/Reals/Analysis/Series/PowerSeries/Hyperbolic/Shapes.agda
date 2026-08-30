module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.CommRing


module HyperbolicAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  half-double-shape : ∀ h a →
    h · (a + a) ≡ (h + h) · a
  half-double-shape h a = solve! R

  sinh-neg-shape : ∀ h a b →
    h · (b + (- a)) ≡ - (h · (a + (- b)))
  sinh-neg-shape h a b = solve! R

  cosh-neg-shape : ∀ h a b →
    h · (b + a) ≡ h · (a + b)
  cosh-neg-shape h a b = solve! R

  exp-neg-derivative-shape : ∀ a →
    a · (- 1r) ≡ - a
  exp-neg-derivative-shape a = solve! R

  sinh-derivative-shape : ∀ h a b →
    h · (a + (- (- b))) ≡ h · (a + b)
  sinh-derivative-shape h a b = solve! R

  addition-coefficient-shape : ∀ h →
    (h · h + h · h) ≡ (h + h) · h
  addition-coefficient-shape h = solve! R

  sinh-add-shape : ∀ h a b c d →
    (h · h + h · h) · (a · c + (- (b · d)))
      ≡
    (h · (a + (- b))) · (h · (c + d)) +
      (h · (a + b)) · (h · (c + (- d)))
  sinh-add-shape h a b c d = solve! R

  cosh-add-shape : ∀ h a b c d →
    (h · h + h · h) · (a · c + b · d)
      ≡
    (h · (a + b)) · (h · (c + d)) +
      (h · (a + (- b))) · (h · (c + (- d)))
  cosh-add-shape h a b c d = solve! R
