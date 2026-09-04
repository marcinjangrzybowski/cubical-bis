module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.RationalPoints where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Nat as ℕ using (ℕ; suc)
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Bisection as RationalBisection

import
  Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as RationalCauchy

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base


-- The historical bisection module uses strict tail indices.  Increasing its
-- selected index by one gives the native non-strict-tail witness used by the
-- sequential completion.

strictRationalCauchy→rationalSeqWitness :
  ∀ points →
  RationalBisection.IsCauchySequenceℚ points →
  RationalCauchy.RationalSeqWitness points
strictRationalCauchy→rationalSeqWitness points cauchy =
  ∣ (λ ε → suc (fst (cauchy ε)))
  , (λ ε m n selected≤m selected≤n →
      snd (cauchy ε) n m selected≤m selected≤n)
  ∣₁


strictRationalCauchy→injectedSeqWitness :
  ∀ points →
  RationalBisection.IsCauchySequenceℚ points →
  SeqWitness (rat ∘ points)
strictRationalCauchy→injectedSeqWitness points cauchy =
  RationalCauchy.rationalSeqWitness→injected points
    (strictRationalCauchy→rationalSeqWitness points cauchy)


-- This record-shaped sigma is the direct output contract for a rational
-- bisection: rational source points, one rational Cauchy witness, interval
-- bounds at every stage, and convergence of their sine images.

RationalPointSineInverseApproximation : ℝ → ℚ → Type₀
RationalPointSineInverseApproximation quarter q =
  Σ[ points ∈ (ℕ → ℚ) ]
    RationalCauchy.RationalSeqWitness points
    × (∀ n →
        ((- quarter) ≤ℝ rat (points n)) ×
        (rat (points n) ≤ℝ quarter))
    × isLimitSequence
        (λ n → sinℝ (rat (points n)))
        (unitClamp (rat q))


RationalPointSineInverseApproximationFamily : ℝ → Type₀
RationalPointSineInverseApproximationFamily quarter =
  (q : ℚ) → RationalPointSineInverseApproximation quarter q


rationalPointSineInverseApproximation→approximation :
  ∀ quarter q →
  RationalPointSineInverseApproximation quarter q →
  RationalSineInverseApproximation quarter q
rationalPointSineInverseApproximation→approximation
    quarter q (points , cauchy , bounds , image-limit) =
  (λ n → rat (points n) , bounds n)
  , RationalCauchy.rationalSeqWitness→injected points cauchy
  , image-limit


rationalPointSineInverseApproximationFamily→approximationFamily :
  ∀ quarter →
  RationalPointSineInverseApproximationFamily quarter →
  RationalSineInverseApproximationFamily quarter
rationalPointSineInverseApproximationFamily→approximationFamily
    quarter approximations q =
  rationalPointSineInverseApproximation→approximation
    quarter q (approximations q)
