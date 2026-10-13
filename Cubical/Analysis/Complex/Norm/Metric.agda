module Cubical.Analysis.Complex.Norm.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_; subZero)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Addition using (<ℝ-add)
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤<ℝ-trans)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
  using (closeness→absDifference<; absDifference<→closeness)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric

closeness→normℂ-difference< : ∀ z w (ε : ℚ₊) → z ∼ℂ[ ε ] w →
  normℂ (z -ℂ w) <ℝ rat (fst ε) + rat (fst ε)
closeness→normℂ-difference< z w ε (real-close , imaginary-close) =
  <ℝ-add (absℝ (re z - re w)) (rat (fst ε)) (absℝ (im z - im w)) (rat (fst ε))
    (closeness→absDifference< (re z) (re w) ε real-close)
    (closeness→absDifference< (im z) (im w) ε imaginary-close)

normℂ-difference<→closeness : ∀ z w (ε : ℚ₊) →
  normℂ (z -ℂ w) <ℝ rat (fst ε) → z ∼ℂ[ ε ] w
normℂ-difference<→closeness z w ε small =
  absDifference<→closeness (re z) (re w) ε
    (≤<ℝ-trans (absℝ (re z - re w)) (normℂ (z -ℂ w)) (rat (fst ε)) (reAbs≤normℂ (z -ℂ w)) small) ,
  absDifference<→closeness (im z) (im w) ε
    (≤<ℝ-trans (absℝ (im z - im w)) (normℂ (z -ℂ w)) (rat (fst ε)) (imAbs≤normℂ (z -ℂ w)) small)

-- Coordinate closeness gives an l1 bound with the sum of the two radii.
-- Callers requesting a norm tolerance can use half that tolerance in each
-- coordinate; there is no implicit identification of the two metrics.
closeZero→normℂ-bound : ∀ z (ε : ℚ₊) → z ∼ℂ[ ε ] 0ℂ →
  normℂ z <ℝ rat (fst ε) + rat (fst ε)
closeZero→normℂ-bound z ε (real-close , imaginary-close) =
  <ℝ-add (absℝ (re z)) (rat (fst ε)) (absℝ (im z)) (rat (fst ε))
    (subst (_<ℝ rat (fst ε)) (cong absℝ (subZero (re z)))
      (closeness→absDifference< (re z) 0ℝ ε real-close))
    (subst (_<ℝ rat (fst ε)) (cong absℝ (subZero (im z)))
      (closeness→absDifference< (im z) 0ℝ ε imaginary-close))
