module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum as ⊎

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.RationalCases
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.RationalCompatibility


opaque
  cosine-absolute-negative-rational : ∀ q →
    rationalAbsolute q ≡ rationalNegation q →
    cosℝ (rat (rationalAbsolute q)) ≡ cosℝ (rat q)
  cosine-absolute-negative-rational q absolute-path =
    cong cosℝ
      (cong rat absolute-path ∙ negation-rational-compatibility q)
    ∙ cosℝ-neg (rat q)


  cosine-absolute-nonnegative-rational : ∀ q →
    rationalAbsolute q ≡ q →
    cosℝ (rat (rationalAbsolute q)) ≡ cosℝ (rat q)
  cosine-absolute-nonnegative-rational q absolute-path =
    cong cosℝ (cong rat absolute-path)


opaque
  cosine-absolute-rational : ∀ q →
    cosℝ (absℝ (rat q)) ≡ cosℝ (rat q)
  cosine-absolute-rational q =
    cong cosℝ (absolute-rational-compatibility q)
    ∙ ⊎.rec
        (cosine-absolute-negative-rational q)
        (cosine-absolute-nonnegative-rational q)
        (rationalAbsoluteCases q)
