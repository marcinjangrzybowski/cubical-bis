module Cubical.Analysis.Complex.Polar.Rotations where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polar.Cis

opaque
  polarℂ-add-pi : ∀ r θ → polarℂ r (θ + piℝ) ≡ -ℂ polarℂ r θ
  polarℂ-add-pi r θ = cong (fromℝ r ·ℂ_) (cisℝ-add θ piℝ)
    ∙ ·ℂAssoc (fromℝ r) (cisℝ θ) (cisℝ piℝ)
    ∙ cong (polarℂ r θ ·ℂ_) cisℝ-pi
    ∙ ·ℂComm (polarℂ r θ) (-ℂ 1ℂ) ∙ sym (ℂRing.-IsMult-1 (polarℂ r θ))

  polarℂ-add-halfPi : ∀ r θ → polarℂ r (θ + halfPiℝ) ≡ iℂ ·ℂ polarℂ r θ
  polarℂ-add-halfPi r θ = cong (fromℝ r ·ℂ_) (cisℝ-add θ halfPiℝ)
    ∙ ·ℂAssoc (fromℝ r) (cisℝ θ) (cisℝ halfPiℝ)
    ∙ cong (polarℂ r θ ·ℂ_) cisℝ-halfPi ∙ ·ℂComm (polarℂ r θ) iℂ

  modulusℂ-i : modulusℂ iℂ ≡ 1ℝ
  modulusℂ-i = cong modulusℂ (sym cisℝ-halfPi) ∙ modulusℂ-cisℝ halfPiℝ

  modulusℂ-negativeQuarterRotate : ∀ z → modulusℂ ((-ℂ iℂ) ·ℂ z) ≡ modulusℂ z
  modulusℂ-negativeQuarterRotate z = modulusℂ-mul (-ℂ iℂ) z
    ∙ cong (_· modulusℂ z) (modulusℂ-neg iℂ ∙ modulusℂ-i) ∙ mulIdL (modulusℂ z)
