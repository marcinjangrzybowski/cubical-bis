module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Parity.Sinh where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Definitions


opaque
  sinhℝ-neg : ∀ x → sinhℝ (Neg.- x) ≡ Neg.- sinhℝ x
  sinhℝ-neg x =
      mul-cong₂-sealed
        {a = halfℝ} {a' = halfℝ}
        {b = expℝ (Neg.- x) Group.- expℝ (Neg.- (Neg.- x))}
        {b' = expℝ (Neg.- x) Group.- expℝ x}
        refl
        (sub-cong₂-sealed
          {a = expℝ (Neg.- x)} {a' = expℝ (Neg.- x)}
          {b = expℝ (Neg.- (Neg.- x))} {b' = expℝ x}
          refl (expℝ-cong-sealed (neg-involutive-sealed x)))
    ∙ HyperbolicAlgebra.sinh-neg-shape ℝCommRing
        halfℝ (expℝ x) (expℝ (Neg.- x))
