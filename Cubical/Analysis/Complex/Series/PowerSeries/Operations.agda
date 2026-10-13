module Cubical.Analysis.Complex.Series.PowerSeries.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing using (CommRingStr)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Base

-- Coefficientwise linear operations preserve supplied sums. These are
-- finite distributivity laws followed by the existing series operations.
addComplexPowerSeriesHasSum : ∀ a b z x y →
  HasComplexSum (powerSeriesTermsℂ a z) x → HasComplexSum (powerSeriesTermsℂ b z) y →
  HasComplexSum (powerSeriesTermsℂ (λ n → a n +ℂ b n) z) (x +ℂ y)
addComplexPowerSeriesHasSum a b z x y first second = complexHasSumPointwise
  (λ n → powerSeriesTermsℂ a z n +ℂ powerSeriesTermsℂ b z n)
  (powerSeriesTermsℂ (λ n → a n +ℂ b n) z)
  (λ n → sym (CommRingStr.·DistL+ (snd ℂCommRing) (a n) (b n) (z ^ℂ n))) (x +ℂ y)
  (addHasComplexSum (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) x y first second)

subComplexPowerSeriesHasSum : ∀ a b z x y →
  HasComplexSum (powerSeriesTermsℂ a z) x → HasComplexSum (powerSeriesTermsℂ b z) y →
  HasComplexSum (powerSeriesTermsℂ (λ n → a n -ℂ b n) z) (x -ℂ y)
subComplexPowerSeriesHasSum a b z x y first second = complexHasSumPointwise
  (λ n → powerSeriesTermsℂ a z n -ℂ powerSeriesTermsℂ b z n)
  (powerSeriesTermsℂ (λ n → a n -ℂ b n) z)
  (λ n → sym (ℂRing.·DistL- (a n) (b n) (z ^ℂ n))) (x -ℂ y)
  (subHasComplexSum (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) x y first second)

scaleComplexPowerSeriesHasSum : ∀ c a z value →
  HasComplexSum (powerSeriesTermsℂ a z) value →
  HasComplexSum (powerSeriesTermsℂ (scaleComplexSeries c a) z) (c ·ℂ value)
scaleComplexPowerSeriesHasSum c a z value summed = complexHasSumPointwise
  (scaleComplexSeries c (powerSeriesTermsℂ a z)) (powerSeriesTermsℂ (scaleComplexSeries c a) z)
  (λ n → ·ℂAssoc c (a n) (z ^ℂ n)) (c ·ℂ value)
  (scaleHasComplexSum c (powerSeriesTermsℂ a z) value summed)
