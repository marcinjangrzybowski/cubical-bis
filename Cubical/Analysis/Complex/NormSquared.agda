module Cubical.Analysis.Complex.NormSquared where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
import Cubical.Analysis.Complex.Algebra.Conjugation as ConjugationDefinition

open ConjugationDefinition.Conjugation ℝCommRing public
  using (normSq; normSq-zero; normSq-one; normSq-neg;
    normSq-conjugate; normSq-mul; mul-conjugate)

normSq-nonnegative : ∀ z → 0ℝ ≤ℝ normSq z
normSq-nonnegative (a , b) = isNonnegative→0≤ (a · a + b · b)
  (addPresIsNonnegative (a · a) (b · b)
    (squareIsNonnegative a) (squareIsNonnegative b))
