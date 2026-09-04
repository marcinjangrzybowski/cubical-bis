module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.CauchyGraph where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire using (sinℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Sequence.Chosen
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence


opaque
  rationalSineInverse-presCauchyGraph :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseLaw inverseℚ →
    RationalSineInverseRange quarter inverseℚ →
    ChosenQuarterTurnSineClosenessReflectionModulus quarter →
    ∀ (source target : ℕ → ℝ) →
    (∀ n → C.JointlyApproximableFor
      inverseℚ (source n) (target n)) →
    SeqWitness source → SeqWitness target
  rationalSineInverse-presCauchyGraph
      quarter inverseℚ inverse-law inverse-range modulus
      source target joint source-witness =
    subst SeqWitness
      (rationalSineInverseGraphPoints-values
        quarter inverseℚ inverse-range source target joint)
      (chosenSineClosenessReflection-presSeqWitness
        quarter modulus
        (λ n → rationalSineInverseGraphPoints
          quarter inverseℚ inverse-range source target joint n)
        (rationalSineInverseGraphPoints-imageSeqWitness
          quarter inverseℚ inverse-law inverse-range
          source target joint source-witness))
