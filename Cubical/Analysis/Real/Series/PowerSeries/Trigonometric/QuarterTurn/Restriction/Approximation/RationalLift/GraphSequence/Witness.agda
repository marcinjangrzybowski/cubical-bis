module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Witness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Points
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Image


opaque
  unitClamp-presSeqWitness : ∀ sequence →
    SeqWitness sequence →
    SeqWitness (unitClamp ∘ sequence)
  unitClamp-presSeqWitness sequence =
    PT.map
      (NE→presIsCauchySeq
        (unitClamp , unitClampIsNonExpanding) sequence)


  rationalSineInverseGraphPoints-imageSeqWitness :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverse-law : RationalSineInverseLaw inverseℚ)
      (inverse-range : RationalSineInverseRange quarter inverseℚ)
      (source target : ℕ → ℝ)
      (joint : ∀ n → C.JointlyApproximableFor
        inverseℚ (source n) (target n)) →
    SeqWitness source →
    SeqWitness (λ n → sinℝ (fst (rationalSineInverseGraphPoints
      quarter inverseℚ inverse-range source target joint n)))
  rationalSineInverseGraphPoints-imageSeqWitness
      quarter inverseℚ inverse-law inverse-range
      source target joint source-witness =
    subst SeqWitness
      (sym (rationalSineInverseGraphPoints-sine-values
        quarter inverseℚ inverse-law inverse-range
        source target joint))
      (unitClamp-presSeqWitness source source-witness)
