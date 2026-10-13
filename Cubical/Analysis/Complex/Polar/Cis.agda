module Cubical.Analysis.Complex.Polar.Cis where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.NormSquared
open import Cubical.Analysis.Complex.Modulus.Base

private
  module R = RingTheory (CommRing→Ring ℝCommRing)
  module Powers = Exponentiation ℂCommRing

opaque
  cisℝ : ℝ → ℂ
  cisℝ θ = cosℝ θ , sinℝ θ

  cisℝ-value : ∀ θ → cisℝ θ ≡ (cosℝ θ , sinℝ θ)
  cisℝ-value θ = refl

  cisℝ-zero : cisℝ 0ℝ ≡ 1ℂ
  cisℝ-zero = ℂ≡ cosℝ-zero sinℝ-zero

  cisℝ-add : ∀ θ φ → cisℝ (θ + φ) ≡ cisℝ θ ·ℂ cisℝ φ
  cisℝ-add θ φ = ℂ≡ (cosℝ-add θ φ)
    (sinℝ-add θ φ ∙ addComm (sinℝ θ · cosℝ φ) (cosℝ θ · sinℝ φ))

  normSq-cisℝ : ∀ θ → normSq (cisℝ θ) ≡ 1ℝ
  normSq-cisℝ θ = addComm (cosℝ θ · cosℝ θ) (sinℝ θ · sinℝ θ) ∙ sin²+cos²≡1 θ

  cisℝ-halfPi : cisℝ halfPiℝ ≡ iℂ
  cisℝ-halfPi = ℂ≡ cosℝ-halfPiℝ sinℝ-halfPiℝ

  cisℝ-pi : cisℝ piℝ ≡ -ℂ 1ℂ
  cisℝ-pi = ℂ≡ cosℝ-piℝ (sinℝ-piℝ ∙ sym R.0Selfinverse)

opaque
  -- De Moivre's formula; the opaque cis keeps the series terms out of the
  -- natural-number induction.
  cisℝ-naturalPower : ∀ θ n → cisℝ θ ^ℂ n ≡ cisℝ (realNatural n · θ)
  cisℝ-naturalPower θ zero = sym cisℝ-zero ∙ cong cisℝ (sym (R.0LeftAnnihilates θ))
  cisℝ-naturalPower θ (suc n) = cong (cisℝ θ ·ℂ_) (cisℝ-naturalPower θ n)
    ∙ sym (cisℝ-add θ (realNatural n · θ))
    ∙ cong cisℝ (sym
      (cong (_· θ) (realNatural-suc n) ∙ mulDistL (realNatural n) 1ℝ θ
        ∙ cong (realNatural n · θ +_) (mulIdL θ) ∙ addComm (realNatural n · θ) θ))

  modulusℂ-cisℝ : ∀ θ → modulusℂ (cisℝ θ) ≡ 1ℝ
  modulusℂ-cisℝ θ = sym (modulusℂ-unique (cisℝ θ) 1ℝ
    (isNonnegative→0≤ 1ℝ oneIsNonnegative) (mulIdR 1ℝ ∙ sym (normSq-cisℝ θ)))

  fromℝ-naturalPower : ∀ x n → fromℝ x ^ℂ n ≡ fromℝ (powℝ x n)
  fromℝ-naturalPower x zero = refl
  fromℝ-naturalPower x (suc n) = cong (fromℝ x ·ℂ_) (fromℝ-naturalPower x n)
    ∙ sym (fromℝ-pres· x (powℝ x n))

polarℂ : ℝ → ℝ → ℂ
polarℂ radius θ = fromℝ radius ·ℂ cisℝ θ

opaque
  polarℂ-naturalPower : ∀ radius θ n → polarℂ radius θ ^ℂ n ≡
    polarℂ (powℝ radius n) (realNatural n · θ)
  polarℂ-naturalPower radius θ n = Powers.^-ldist-· (fromℝ radius) (cisℝ θ) n
    ∙ cong₂ _·ℂ_ (fromℝ-naturalPower radius n) (cisℝ-naturalPower θ n)
