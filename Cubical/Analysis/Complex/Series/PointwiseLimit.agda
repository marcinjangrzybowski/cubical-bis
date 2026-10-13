module Cubical.Analysis.Complex.Series.PointwiseLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
import Cubical.Analysis.Real.Series.PointwiseLimit as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform

-- Coordinate adapters for the native real limit-interchange theorems.
partialSumℂPresPointwiseLimit : ∀ (terms : ℕ → ComplexSequence) values →
  (∀ k → IsComplexLimit (λ index → terms index k) (values k)) → ∀ count →
  IsComplexLimit (λ index → partialSumℂ (terms index) count) (partialSumℂ values count)
partialSumℂPresPointwiseLimit terms values pointwise count =
  Real.partialSumPresPointwiseLimit (λ index → re ∘ terms index) (re ∘ values) (fst ∘ pointwise) count ,
  Real.partialSumPresPointwiseLimit (λ index → im ∘ terms index) (im ∘ values) (snd ∘ pointwise) count

uniformlyComplexCauchyPointwiseLimitIsCauchy : ∀ (terms : ℕ → ComplexSequence) values →
  UniformlyComplexCauchySeries ℕ terms →
  (∀ k → IsComplexLimit (λ index → terms index k) (values k)) → IsComplexCauchySeries values
uniformlyComplexCauchyPointwiseLimitIsCauchy terms values uniform pointwise =
  Real.uniformlyCauchyPointwiseLimitIsCauchy (λ index → re ∘ terms index) (re ∘ values) (fst uniform) (fst ∘ pointwise) ,
  Real.uniformlyCauchyPointwiseLimitIsCauchy (λ index → im ∘ terms index) (im ∘ values) (snd uniform) (snd ∘ pointwise)

uniformComplexSeriesSumsPresPointwiseLimit : ∀ (terms : ℕ → ComplexSequence) values sums value →
  UniformHasComplexSum terms sums →
  (∀ k → IsComplexLimit (λ index → terms index k) (values k)) →
  HasComplexSum values value → IsComplexLimit sums value
uniformComplexSeriesSumsPresPointwiseLimit terms values sums value uniform pointwise summed =
  Real.uniformSeriesSumsPresPointwiseLimit (λ index → re ∘ terms index) (re ∘ values) (re ∘ sums) (re value)
    (fst uniform) (fst ∘ pointwise) (fst summed) ,
  Real.uniformSeriesSumsPresPointwiseLimit (λ index → im ∘ terms index) (im ∘ values) (im ∘ sums) (im value)
    (snd uniform) (snd ∘ pointwise) (snd summed)
