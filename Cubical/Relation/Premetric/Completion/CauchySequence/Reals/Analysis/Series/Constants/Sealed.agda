module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Constants.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


-- The series layer's ring constants are definitionally the embedded rational
-- constants.  Naming that conversion keeps it from being rediscovered by
-- normalization inside larger analytic paths.
opaque
  rationalZero≡zeroℝ : Real.ιℚ 0 ≡ zeroℝ
  rationalZero≡zeroℝ = refl


  neg-zeroℝ-sealed : Neg.- zeroℝ ≡ zeroℝ
  neg-zeroℝ-sealed =
      cong Neg.-_ (sym rationalZero≡zeroℝ)
    ∙ neg-zero-sealed
    ∙ rationalZero≡zeroℝ
