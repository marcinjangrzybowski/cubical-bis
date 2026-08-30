module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Agreement.Cosh where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Definitions
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Definitions


opaque
  sealedCoshℝ-agrees : sealedCoshℝ ≡ coshℝ
  sealedCoshℝ-agrees =
    funExt λ x →
      mul-cong₂-sealed
        {a = halfℝ} {a' = halfℝ}
        {b = sealedExpℝ x Add.+ sealedExpℝ (Neg.- x)}
        {b' = expℝ x Add.+ expℝ (Neg.- x)}
        refl
        (add-cong₂-sealed
          {a = sealedExpℝ x} {a' = expℝ x}
          {b = sealedExpℝ (Neg.- x)} {b' = expℝ (Neg.- x)}
          (sealedExpℝ-agrees x)
          (sealedExpℝ-agrees (Neg.- x)))
