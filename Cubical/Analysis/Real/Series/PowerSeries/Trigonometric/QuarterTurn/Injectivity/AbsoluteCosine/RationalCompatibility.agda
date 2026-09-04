module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.RationalCompatibility where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.RationalCases


opaque
  absolute-rational-compatibility : ∀ q →
    absℝ (rat q) ≡ rat (rationalAbsolute q)
  absolute-rational-compatibility = abs-rat


  negation-rational-compatibility : ∀ q →
    rat (rationalNegation q) ≡ - rat q
  negation-rational-compatibility q = sym (neg-rat q)
