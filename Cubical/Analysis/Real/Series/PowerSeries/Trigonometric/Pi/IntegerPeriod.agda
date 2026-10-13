module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.IntegerPeriod where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Fast using (ℤ; pos; negsuc)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  opaque
    positiveMultipleStep : ∀ n p →
      integer (pos (suc n)) · p ≡ p + integer (pos n) · p
    positiveMultipleStep n p = cong (_· p) (sym (integer-add (pos 1) (pos n)))
      ∙ mulDistL 1ℝ (integer (pos n)) p
      ∙ cong (_+ integer (pos n) · p) (mulIdL p)

    negativeMultiple : ∀ n p →
      integer (negsuc n) · p ≡ - (integer (pos (suc n)) · p)
    negativeMultiple n p = cong (_· p) (sym (integer-neg (pos (suc n))))
      ∙ R.-DistL· (integer (pos (suc n))) p

  opaque
    periodicNatural : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ f x) →
      ∀ n x → f (x + integer (pos n) · p) ≡ f x
    periodicNatural f p period zero x =
      cong f (cong (x +_) (R.0LeftAnnihilates p) ∙ addIdR x)
    periodicNatural f p period (suc n) x =
      cong f (cong (x +_) (positiveMultipleStep n p)
        ∙ addAssoc x p (integer (pos n) · p))
      ∙ periodicNatural f p period n (x + p) ∙ period x

  opaque
    periodicInteger : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ f x) →
      ∀ k x → f (x + integer k · p) ≡ f x
    periodicInteger f p period (pos n) x = periodicNatural f p period n x
    periodicInteger f p period (negsuc n) x =
      cong f (cong (x +_) (negativeMultiple n p))
      ∙ sym (periodicNatural f p period (suc n) (x - integer (pos (suc n)) · p))
      ∙ cong f (subAddCancel x (integer (pos (suc n)) · p))

  opaque
    periodValue : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ f x) →
      ∀ k → f (integer k · p) ≡ f 0ℝ
    periodValue f p period k = cong f (sym (addIdL (integer k · p)))
      ∙ periodicInteger f p period k 0ℝ

    scaledRelated : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ f x) →
      ∀ x y k → x - y ≡ integer k → f (x · p) ≡ f (y · p)
    scaledRelated f p period x y k difference =
      cong f (sym (subAddCancel (x · p) (y · p))
        ∙ cong (_+ y · p) (sym (R.·DistL- x y p) ∙ cong (_· p) difference)
        ∙ addComm (integer k · p) (y · p))
      ∙ periodicInteger f p period k (y · p)

opaque
  sinℝ-integer-period : ∀ k x → sinℝ (x + integer k · twoPiℝ) ≡ sinℝ x
  sinℝ-integer-period = periodicInteger sinℝ twoPiℝ sinℝ-periodic

  cosℝ-integer-period : ∀ k x → cosℝ (x + integer k · twoPiℝ) ≡ cosℝ x
  cosℝ-integer-period = periodicInteger cosℝ twoPiℝ cosℝ-periodic

  sinℝ-integer-twoPiℝ : ∀ k → sinℝ (integer k · twoPiℝ) ≡ 0ℝ
  sinℝ-integer-twoPiℝ k = periodValue sinℝ twoPiℝ sinℝ-periodic k ∙ sinℝ-zero

  cosℝ-integer-twoPiℝ : ∀ k → cosℝ (integer k · twoPiℝ) ≡ 1ℝ
  cosℝ-integer-twoPiℝ k = periodValue cosℝ twoPiℝ cosℝ-periodic k ∙ cosℝ-zero

  -- The turn-coordinate form used by the HIT circle development, proved
  -- here directly for Analysis reals and their native integer embedding.
  sinℝ-equal-turns : ∀ x y k → x - y ≡ integer k →
    sinℝ (x · twoPiℝ) ≡ sinℝ (y · twoPiℝ)
  sinℝ-equal-turns = scaledRelated sinℝ twoPiℝ sinℝ-periodic

  cosℝ-equal-turns : ∀ x y k → x - y ≡ integer k →
    cosℝ (x · twoPiℝ) ≡ cosℝ (y · twoPiℝ)
  cosℝ-equal-turns = scaledRelated cosℝ twoPiℝ cosℝ-periodic
