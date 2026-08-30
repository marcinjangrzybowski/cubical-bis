module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Integral.PointwiseClose where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Inverse
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
  using (limits-preserve-closeness-below)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Close


-- Passing the uniform error estimate through both canonical completions
-- gives a genuine Lipschitz-style estimate for the constructed integral.
-- No convergence index in the dyadic depth is selected.

recursiveDyadicIntegral-pointwiseClose :
  ∀ a b (a≤b : a ≤ℝ b) B f g
  (f-uc : IsRadiuswiseUniformlyContinuousℝ f)
  (g-uc : IsRadiuswiseUniformlyContinuousℝ g) ε →
  Abs.absℝ (b Group.- a) ≤ℝ Real.ιℚ (fst B) →
  (∀ x → a ≤ℝ x → x ≤ℝ b →
    f x Real.Base.≈ᶜ[ (((ε /2₊) /2₊) ₊／₊ B) ] g x) →
  recursiveDyadicIntegral f a b a≤b f-uc
    Real.Base.≈ᶜ[ ε ]
  recursiveDyadicIntegral g a b a≤b g-uc
recursiveDyadicIntegral-pointwiseClose
  a b a≤b B f g f-uc g-uc ε width-bound pointwise =
  limits-preserve-closeness-below
    (recursiveDyadicIntegralCauchy f a b a≤b f-uc)
    (recursiveDyadicIntegralCauchy g a b a≤b g-uc)
    (ε /2₊) ε (/2₊<id ε)
    (λ n → dyadicRecursiveSum-pointwiseClose
      f g a b ε B n width-bound a≤b pointwise)
