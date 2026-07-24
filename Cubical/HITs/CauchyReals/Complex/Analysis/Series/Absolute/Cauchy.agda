module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Cauchy where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Base
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Distance


opaque
  absoluteConvergence→cauchy : (terms : ComplexSequence) →
    IsAbsolutelyConvergentSeriesℂ terms →
    IsCauchySeriesℂ terms
  absoluteConvergence→cauchy terms absolute =
    (λ ε → suc (fst (absolute ε))) ,
    λ ε m n index≤m index≤n →
      isTrans≤<ᵣ _ _ _
        (partialSum-distance-bound terms m n)
        (snd (absolute ε) n m index≤m index≤n)


absolutelyConvergentSeriesHasLimit : (terms : ComplexSequence) →
  IsAbsolutelyConvergentSeriesℂ terms →
  HasComplexLimit (partialSumℂ terms)
absolutelyConvergentSeriesHasLimit terms absolute =
  sumCauchySeries terms
    (absoluteConvergence→cauchy terms absolute)
