module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Agreement.Sinh where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Definitions
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Definitions


opaque
  sealedSinhℝ-agrees : sealedSinhℝ ≡ sinhℝ
  sealedSinhℝ-agrees =
    funExt λ x →
      mul-cong₂-sealed
        {a = halfℝ} {a' = halfℝ}
        {b = sealedExpℝ x Group.- sealedExpℝ (Neg.- x)}
        {b' = expℝ x Group.- expℝ (Neg.- x)}
        refl
        (sub-cong₂-sealed
          {a = sealedExpℝ x} {a' = expℝ x}
          {b = sealedExpℝ (Neg.- x)} {b' = expℝ (Neg.- x)}
          (sealedExpℝ-agrees x)
          (sealedExpℝ-agrees (Neg.- x)))
