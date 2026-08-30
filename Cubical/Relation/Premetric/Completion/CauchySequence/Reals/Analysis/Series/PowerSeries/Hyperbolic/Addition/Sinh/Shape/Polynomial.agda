module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Shape.Polynomial where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Terms
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Shape.Transport

opaque
  sinhℝ-add-polynomial : ∀ x y →
    sinhAddScaled x y ≡ sinhAddShaped x y
  sinhℝ-add-polynomial x y =
    sinh-add-shape-concrete
      halfℝ
      (expℝ x) (expℝ (Neg.- x))
      (expℝ y) (expℝ (Neg.- y))
