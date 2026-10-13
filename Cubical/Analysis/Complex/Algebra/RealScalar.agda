module Cubical.Analysis.Complex.Algebra.RealScalar where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra

private module R = Ring.RingTheory (CommRing→Ring ℝCommRing)

fromℝDifference : ∀ x y → fromℝ x -ℂ fromℝ y ≡ fromℝ (x - y)
fromℝDifference x y = ℂ≡ refl (subSelf 0ℝ)

-- Shared by horizontal restriction and differentiation of real-parameter
-- curves. A real increment acts separately on the two coordinates.
complexMultiplyReal : ∀ d t → d ·ℂ fromℝ t ≡ (re d · t , im d · t)
complexMultiplyReal d t = ℂ≡
  (cong (re d · t -_) (R.0RightAnnihilates (im d)) ∙ subZero (re d · t))
  (cong (_+ im d · t) (R.0RightAnnihilates (re d)) ∙ addIdL (im d · t))
