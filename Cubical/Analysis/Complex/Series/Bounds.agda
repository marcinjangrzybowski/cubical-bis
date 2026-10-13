module Cubical.Analysis.Complex.Series.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually using (pointwiseLePresLimits)
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Bounds as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Base

opaque
  partialSumℂNormBound : ∀ terms n → normℂ (partialSumℂ terms n) ≤ℝ Real.partialSum (normℂ ∘ terms) n
  partialSumℂNormBound terms n = subst (normℂ (partialSumℂ terms n) ≤ℝ_)
    (sym (Real.partialSum-add (absℝ ∘ re ∘ terms) (absℝ ∘ im ∘ terms) n))
    (addPres≤ (absℝ (Real.partialSum (re ∘ terms) n)) (Real.partialSum (absℝ ∘ re ∘ terms) n)
      (absℝ (Real.partialSum (im ∘ terms) n)) (Real.partialSum (absℝ ∘ im ∘ terms) n)
      (Real.partialSumAbsBound (re ∘ terms) n) (Real.partialSumAbsBound (im ∘ terms) n))

  partialSumℂBoundBy : ∀ terms bound → (∀ n → normℂ (terms n) ≤ℝ bound n) →
    ∀ n → normℂ (partialSumℂ terms n) ≤ℝ Real.partialSum bound n
  partialSumℂBoundBy terms bound dominates n = ≤ℝ-trans
    (normℂ (partialSumℂ terms n)) (Real.partialSum (normℂ ∘ terms) n) (Real.partialSum bound n)
    (partialSumℂNormBound terms n) (Real.partialSumMono (normℂ ∘ terms) bound dominates n)

  -- This bound consumes both sums. It asserts no existence from mere
  -- convergence of a majorant; construction uses the stronger Cauchy input.
  seriesSumℂBoundBy : ∀ terms bound (summed : ComplexSummable terms) (majorant : Real.Summable bound) →
    (∀ n → normℂ (terms n) ≤ℝ bound n) → normℂ (seriesSumℂ terms summed) ≤ℝ Real.seriesSum bound majorant
  seriesSumℂBoundBy terms bound summed majorant dominates = pointwiseLePresLimits
    (partialSumℂBoundBy terms bound dominates) (normℂ-preservesLimit (snd summed)) (snd majorant)
