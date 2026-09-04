module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Mappings
import
  Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Order.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


module C =
  CauchyContinuousDefinition ℚPremetricSpace ℚPremetricSpace


unitClamp : ℝ → ℝ
unitClamp = clampInterval (- 1ℝ) 1ℝ


unitClampPres∼ : ∀ x y ε →
  x ∼[ ε ] y → unitClamp x ∼[ ε ] unitClamp y
unitClampPres∼ = clampIntervalPres∼ (- 1ℝ) 1ℝ


unitClampIsNonExpanding :
  IsNonExpanding
    (ℝPremetricSpace .snd) unitClamp
    (ℝPremetricSpace .snd)
unitClampIsNonExpanding .IsNonExpanding.pres≈ =
  unitClampPres∼


unitClampFix : ∀ x →
  (- 1ℝ) ≤ℝ x → x ≤ℝ 1ℝ → unitClamp x ≡ x
unitClampFix = clampIntervalFix (- 1ℝ) 1ℝ


quarterClamp : ℝ → ℝ → ℝ
quarterClamp quarter = clampInterval (- quarter) quarter


quarterClampPres∼ : ∀ quarter x y ε →
  x ∼[ ε ] y →
  quarterClamp quarter x ∼[ ε ] quarterClamp quarter y
quarterClampPres∼ quarter =
  clampIntervalPres∼ (- quarter) quarter


quarterClampFix : ∀ quarter x →
  (- quarter) ≤ℝ x → x ≤ℝ quarter →
  quarterClamp quarter x ≡ x
quarterClampFix quarter =
  clampIntervalFix (- quarter) quarter


RationalSineInverseCandidate : Type₀
RationalSineInverseCandidate = ℚ → ℝ


RationalSineInverseLaw : RationalSineInverseCandidate → Type₀
RationalSineInverseLaw inverseℚ =
  ∀ q → sinℝ (inverseℚ q) ≡ unitClamp (rat q)


RationalSineInverseRange :
  ℝ → RationalSineInverseCandidate → Type₀
RationalSineInverseRange quarter inverseℚ =
  ∀ q → ((- quarter) ≤ℝ inverseℚ q) ×
        (inverseℚ q ≤ℝ quarter)


RationalSineInverseData : ℝ → Type₀
RationalSineInverseData quarter =
  Σ[ inverseℚ ∈ RationalSineInverseCandidate ]
    C.IsCauchyContinuous inverseℚ ×
    RationalSineInverseLaw inverseℚ ×
    RationalSineInverseRange quarter inverseℚ


RationalSineInverseConstruction : ℝ → Type₀
RationalSineInverseConstruction quarter =
  Σ[ inverseℚ ∈ RationalSineInverseCandidate ]
    RationalSineInverseLaw inverseℚ ×
    RationalSineInverseRange quarter inverseℚ


liftRationalSineInverse :
  (inverseℚ : RationalSineInverseCandidate) →
  C.IsCauchyContinuous inverseℚ →
  ℝ → ℝ
liftRationalSineInverse = C.liftCauchyContinuous
