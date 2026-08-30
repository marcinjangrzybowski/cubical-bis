module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Constants
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Terms
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.AtZero
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Parity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Shape

opaque
  one≡coshSquare-sub-sinhSquare : ∀ x →
    oneℝ ≡ (coshℝ x Mul.· coshℝ x) Group.-
      (sinhℝ x Mul.· sinhℝ x)
  one≡coshSquare-sub-sinhSquare x =
      one≡cosh-add-inverse x
    ∙ cosh-add-inverse≡translated x
    ∙ fundamentalTranslated≡parity x
    ∙ fundamentalParity≡difference x

  coshSquare-sub-sinhSquare≡one : ∀ x →
    (coshℝ x Mul.· coshℝ x) Group.-
        (sinhℝ x Mul.· sinhℝ x) ≡ oneℝ
  coshSquare-sub-sinhSquare≡one x =
    sym (one≡coshSquare-sub-sinhSquare x)
