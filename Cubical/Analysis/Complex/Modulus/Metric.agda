module Cubical.Analysis.Complex.Modulus.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds

modulusℂ-difference<→closeness : ∀ z w (ε : ℚ₊) →
  modulusℂ (z -ℂ w) <ℝ rat (fst ε) → z ∼ℂ[ ε ] w
modulusℂ-difference<→closeness z w ε small =
  absDifference<→closeness (re z) (re w) ε
    (≤<ℝ-trans (absℝ (re z - re w)) (modulusℂ (z -ℂ w)) (rat (fst ε))
      (reAbs≤modulusℂ (z -ℂ w)) small) ,
  absDifference<→closeness (im z) (im w) ε
    (≤<ℝ-trans (absℝ (im z - im w)) (modulusℂ (z -ℂ w)) (rat (fst ε))
      (imAbs≤modulusℂ (z -ℂ w)) small)

modulusℂ-small→closeZero : ∀ z (ε : ℚ₊) →
  modulusℂ z <ℝ rat (fst ε) → z ∼ℂ[ ε ] 0ℂ
modulusℂ-small→closeZero z ε small =
  absDifference<→closeness (re z) 0ℝ ε
    (subst (_<ℝ rat (fst ε)) (sym (cong absℝ (subZero (re z))))
      (≤<ℝ-trans (absℝ (re z)) (modulusℂ z) (rat (fst ε)) (reAbs≤modulusℂ z) small)) ,
  absDifference<→closeness (im z) 0ℝ ε
    (subst (_<ℝ rat (fst ε)) (sym (cong absℝ (subZero (im z))))
      (≤<ℝ-trans (absℝ (im z)) (modulusℂ z) (rat (fst ε)) (imAbs≤modulusℂ z) small))
