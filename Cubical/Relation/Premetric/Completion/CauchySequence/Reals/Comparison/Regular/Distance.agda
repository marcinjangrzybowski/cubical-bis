module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Distance where

open import Cubical.Foundations.Prelude

import Cubical.HITs.CauchyRealsP.Algebra.Negation as CRNeg
import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue as CRAbs
import Cubical.HITs.CauchyRealsP.Algebra.Addition as CRAdd
open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as RealNeg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as RealAbs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as RealAdd
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance
  as RealDistance
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as Comparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Algebra
  as ComparisonAlgebra


regularDistance : CR.ℝ → CR.ℝ → CR.ℝ
regularDistance x y =
  CRAbs.absℝ (CRAdd._+_ x (CRNeg.- y))

fromRegular-presDistance : ∀ x y →
  Comparison.fromRegular (regularDistance x y) ≡
  RealDistance.distance
    (Comparison.fromRegular x)
    (Comparison.fromRegular y)
fromRegular-presDistance x y =
    ComparisonAlgebra.fromRegular-presAbsoluteValue
      (CRAdd._+_ x (CRNeg.- y))
  ∙ cong RealAbs.absℝ
      (ComparisonAlgebra.fromRegular-presAddition
        x (CRNeg.- y)
      ∙ cong (RealAdd._+_
          (Comparison.fromRegular x))
          (ComparisonAlgebra.fromRegular-presNegation y))
