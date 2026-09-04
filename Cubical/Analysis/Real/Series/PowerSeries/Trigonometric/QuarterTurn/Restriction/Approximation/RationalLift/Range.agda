module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Range where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
import Cubical.Analysis.Real.Algebra.Negation as Neg
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Order.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
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


opaque
  rationalSineInverseGraph-clamp :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseRange quarter inverseℚ →
    ∀ target lifted →
    C.JointlyApproximableFor inverseℚ target lifted →
    lifted ≡ quarterClamp quarter lifted
  rationalSineInverseGraph-clamp
      quarter inverseℚ inverse-range target lifted joint =
    eqℝ lifted (quarterClamp quarter lifted) close
    where
    close : ∀ ε → lifted ∼[ ε ] quarterClamp quarter lifted
    close ε =
      PT.rec
        (S.isProp∼ lifted ε (quarterClamp quarter lifted))
        with-rational
        (joint ε (ε /4₊))
      where
      with-rational :
        (Σ[ q ∈ _ ]
          (rat q ∼[ ε ] target) ×
          (inverseℚ q ∼[ ε /4₊ ] lifted)) →
        lifted ∼[ ε ] quarterClamp quarter lifted
      with-rational (q , _ , inverseq-close) =
        S.isMonotone∼̂ₛ<
          lifted (quarterClamp quarter lifted)
          (ε /4₊ +₊ ε /4₊) ε (twoQuarter< ε)
          (triangle∼
            lifted (inverseℚ q) (quarterClamp quarter lifted)
            (ε /4₊) (ε /4₊)
            (sym∼ (inverseℚ q) lifted (ε /4₊) inverseq-close)
            (subst
              (λ value →
                value ∼[ ε /4₊ ] quarterClamp quarter lifted)
              (quarterClampFix quarter (inverseℚ q)
                (fst (inverse-range q))
                (snd (inverse-range q)))
              (quarterClampPres∼ quarter
                (inverseℚ q) lifted (ε /4₊) inverseq-close)))


  rationalSineInverseGraph-inQuarter :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseRange quarter inverseℚ →
    ∀ target output →
    C.JointlyApproximableFor inverseℚ target output →
    SineQuarterInterval quarter
  rationalSineInverseGraph-inQuarter
      quarter inverseℚ inverse-range target output joint =
    output , lower-bound , upper-bound
    where
    output-clamp : output ≡ quarterClamp quarter output
    output-clamp =
      rationalSineInverseGraph-clamp
        quarter inverseℚ inverse-range target output joint

    lower-bound : Neg.- quarter ≤ℝ output
    lower-bound = subst ((Neg.- quarter) ≤ℝ_)
      (sym output-clamp)
      (clampIntervalLowerBound
        (Neg.- quarter) quarter output)

    endpoints-ordered : Neg.- quarter ≤ℝ quarter
    endpoints-ordered =
      ≤ℝ-trans
        (Neg.- quarter) (inverseℚ 0) quarter
        (fst (inverse-range 0))
        (snd (inverse-range 0))

    upper-bound : output ≤ℝ quarter
    upper-bound = subst (_≤ℝ quarter)
      (sym output-clamp)
      (clampIntervalUpperBound
        (Neg.- quarter) quarter endpoints-ordered output)


  rationalSineInverseGraph-inQuarter-value :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverse-range : RationalSineInverseRange quarter inverseℚ)
      target output
      (joint : C.JointlyApproximableFor inverseℚ target output) →
    fst (rationalSineInverseGraph-inQuarter
      quarter inverseℚ inverse-range target output joint) ≡ output
  rationalSineInverseGraph-inQuarter-value
      quarter inverseℚ inverse-range target output joint = refl


  liftRationalSineInverse-inQuarter :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverseℚ-cc : C.IsCauchyContinuous inverseℚ) →
      RationalSineInverseRange quarter inverseℚ →
      ∀ (target : ℝ) → SineQuarterInterval quarter
  liftRationalSineInverse-inQuarter
      quarter inverseℚ inverseℚ-cc inverse-range target =
    lifted , lower-bound , upper-bound
    where
    lifted : ℝ
    lifted = liftRationalSineInverse inverseℚ inverseℚ-cc target

    lifted-clamp : lifted ≡ quarterClamp quarter lifted
    lifted-clamp =
      rationalSineInverseGraph-clamp
        quarter inverseℚ inverse-range target lifted
        (C.liftCauchyContinuous-joint
          inverseℚ inverseℚ-cc target)

    lower-bound : Neg.- quarter ≤ℝ lifted
    lower-bound = subst ((Neg.- quarter) ≤ℝ_)
      (sym lifted-clamp)
      (clampIntervalLowerBound
        (Neg.- quarter) quarter lifted)

    endpoints-ordered : Neg.- quarter ≤ℝ quarter
    endpoints-ordered =
      ≤ℝ-trans
        (Neg.- quarter) (inverseℚ 0) quarter
        (fst (inverse-range 0))
        (snd (inverse-range 0))

    upper-bound : lifted ≤ℝ quarter
    upper-bound = subst (_≤ℝ quarter)
      (sym lifted-clamp)
      (clampIntervalUpperBound
        (Neg.- quarter) quarter endpoints-ordered lifted)


  liftRationalSineInverse-inQuarter-value :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverseℚ-cc : C.IsCauchyContinuous inverseℚ)
      (inverse-range : RationalSineInverseRange quarter inverseℚ)
      (target : ℝ) →
    fst (liftRationalSineInverse-inQuarter
      quarter inverseℚ inverseℚ-cc inverse-range target)
      ≡ liftRationalSineInverse inverseℚ inverseℚ-cc target
  liftRationalSineInverse-inQuarter-value
      quarter inverseℚ inverseℚ-cc inverse-range target = refl
