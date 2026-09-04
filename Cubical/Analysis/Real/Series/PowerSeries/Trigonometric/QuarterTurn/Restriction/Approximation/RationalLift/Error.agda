module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Error where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base


open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


private
  twoQuarter< : ∀ ε → (ε /4₊ +₊ ε /4₊) <₊ ε
  twoQuarter< ε = begin<
    fst (ε /4₊ +₊ ε /4₊)
      ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
    fst (ε /2₊)
      <⟨ /2₊<id ε ⟩
    fst ε ◾


rationalSineInverseApproximation-close :
  ∀ (inverseℚ : RationalSineInverseCandidate) →
  RationalSineInverseLaw inverseℚ →
  ∀ target lifted ε δ →
  (∀ point → lifted ∼[ δ ] point →
    sinℝ lifted ∼[ ε /4₊ ] sinℝ point) →
  (Σ[ q ∈ ℚ ]
    (rat q ∼[ ε /4₊ ] target) ×
    (inverseℚ q ∼[ δ ] lifted)) →
  sinℝ lifted ∼[ ε ] unitClamp target
rationalSineInverseApproximation-close
    inverseℚ inverse-law target lifted ε δ preserves
    (q , ratq-close , inverseq-close) =
  S.isMonotone∼̂ₛ<
    (sinℝ lifted) (unitClamp target)
    (ε /4₊ +₊ ε /4₊) ε (twoQuarter< ε)
    (triangle∼
      (sinℝ lifted) (sinℝ (inverseℚ q))
      (unitClamp target) (ε /4₊) (ε /4₊)
      (preserves (inverseℚ q)
        (sym∼ (inverseℚ q) lifted δ inverseq-close))
      (subst
        (λ value → value ∼[ ε /4₊ ] unitClamp target)
        (sym (inverse-law q))
        (unitClampPres∼ (rat q) target (ε /4₊) ratq-close)))
