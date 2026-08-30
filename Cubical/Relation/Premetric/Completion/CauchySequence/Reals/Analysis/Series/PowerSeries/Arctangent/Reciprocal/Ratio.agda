module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Ratio where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Uniform
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Data.Rationals.Order as ℚ

arctangentClosedPointAbs<one :
  ∀ (q : ℚ₊) → fst q ℚ.< 1 →
  (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
  Abs.absℝ (fst point) <ℝ oneℝ
arctangentClosedPointAbs<one q q<1 point =
  ≤<ℝ-trans
    (Abs.absℝ (fst point)) (Real.ιℚ (fst q)) oneℝ
    (snd point) (<ℚ→<ℝ (fst q) 1 q<1)

arctangentRatio : Real.ℝ → Real.ℝ
arctangentRatio x = Neg.- (x Mul.· x)

opaque
  arctangentRatioAbs<one :
    ∀ (q : ℚ₊) (q<1 : fst q ℚ.< 1)
      (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
    Abs.absℝ (arctangentRatio (fst point)) <ℝ oneℝ
  arctangentRatioAbs<one q q<1 point =
    subst (_<ℝ oneℝ) (sym absolute-ratio-path) square<one
    where
    x : Real.ℝ
    x = fst point

    absolute-ratio-path :
      Abs.absℝ (arctangentRatio x)
        ≡ Abs.absℝ x Mul.· Abs.absℝ x
    absolute-ratio-path = Abs.absℝ-neg (x Mul.· x) ∙ abs-mul x x

    square≤self :
      Abs.absℝ x Mul.· Abs.absℝ x ≤ℝ Abs.absℝ x
    square≤self =
      subst
        (Abs.absℝ x Mul.· Abs.absℝ x ≤ℝ_)
        (mul-one-right (Abs.absℝ x))
        (mul-preserves≤-left-nonnegative
          (Abs.absℝ x) oneℝ (Abs.absℝ x)
          (<ℝ-weaken (Abs.absℝ x) oneℝ
            (arctangentClosedPointAbs<one q q<1 point))
          (zero≤abs x))

    square<one :
      Abs.absℝ x Mul.· Abs.absℝ x <ℝ oneℝ
    square<one =
      ≤<ℝ-trans
        (Abs.absℝ x Mul.· Abs.absℝ x)
        (Abs.absℝ x) oneℝ square≤self
        (arctangentClosedPointAbs<one q q<1 point)

arctangentRatio<one :
  ∀ (q : ℚ₊) (q<1 : fst q ℚ.< 1)
    (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
  arctangentRatio (fst point) <ℝ oneℝ
arctangentRatio<one q q<1 point =
  ≤<ℝ-trans
    (arctangentRatio (fst point))
    (Abs.absℝ (arctangentRatio (fst point))) oneℝ
    (x≤abs (arctangentRatio (fst point)))
    (arctangentRatioAbs<one q q<1 point)
