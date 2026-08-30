module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes


halfℚ : ℚ
halfℚ = fst (1₊ /2₊)

halfℝ : Real.ℝ
halfℝ = Real.ιℚ halfℚ

oneℝ : Real.ℝ
oneℝ = Real.ιℚ 1

half-plus-half : halfℝ Add.+ halfℝ ≡ oneℝ
half-plus-half =
    Add.add-ι-ι halfℚ halfℚ
  ∙ cong Real.ιℚ (/2+/2≡id 1)


opaque
  twice-half-squared :
    (halfℝ Mul.· halfℝ) Add.+ (halfℝ Mul.· halfℝ)
      ≡ halfℝ
  twice-half-squared =
      HyperbolicAlgebra.addition-coefficient-shape ℝCommRing halfℝ
    ∙ cong (Mul._· halfℝ) half-plus-half
    ∙ mul-one-left halfℝ
