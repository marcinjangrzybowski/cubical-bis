module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh.OutputAgreement where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Definitions


-- The derivative of the difference contains a double negation.  Keep the
-- completion-level normalization behind a small path between whole functions.

opaque
  sealedSinhDerivative-agrees :
    (λ x → halfℝ Mul.·
      (sealedExpℝ x Group.- (Neg.- sealedExpℝ (Neg.- x))))
      ≡ sealedCoshℝ
  sealedSinhDerivative-agrees = funExt λ x →
    mul-cong₂-sealed
      {a = halfℝ}
      {a' = halfℝ}
      {b = sealedExpℝ x Group.- (Neg.- sealedExpℝ (Neg.- x))}
      {b' = sealedExpℝ x Add.+ sealedExpℝ (Neg.- x)}
      refl
      (add-cong₂-sealed
        {a = sealedExpℝ x}
        {a' = sealedExpℝ x}
        {b = Neg.- (Neg.- sealedExpℝ (Neg.- x))}
        {b' = sealedExpℝ (Neg.- x)}
        refl
        (neg-involutive-sealed (sealedExpℝ (Neg.- x))))
