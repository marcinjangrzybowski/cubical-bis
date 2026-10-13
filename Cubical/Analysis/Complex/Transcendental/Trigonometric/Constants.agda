module Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using ([_/_]; eq/)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra

halfℝ : ℝ
halfℝ = rat [ pos 1 / 1+ 1 ]

halfℂ : ℂ
halfℂ = fromℝ halfℝ

opaque
  halfℝ-double : halfℝ + halfℝ ≡ 1ℝ
  halfℝ-double = rat+rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl)

  halfℂ-double : halfℂ +ℂ halfℂ ≡ 1ℂ
  halfℂ-double = sym (fromℝ-pres+ halfℝ halfℝ) ∙ cong fromℝ halfℝ-double
