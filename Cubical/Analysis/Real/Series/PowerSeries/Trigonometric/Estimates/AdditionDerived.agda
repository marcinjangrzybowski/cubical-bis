module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


-- Subtraction formulas are immediate consequences of the total addition
-- laws and parity.  Keeping them named avoids repeating ring normalization
-- in later estimates.

opaque
  sinℝ-sub : ∀ x y →
    sinℝ (x - y)
      ≡
    (sinℝ x · cosℝ y) - (cosℝ x · sinℝ y)
  sinℝ-sub x y =
    sinℝ-add x (- y)
    ∙ cong₂ _+_
        (cong (sinℝ x ·_) (cosℝ-neg y))
        (cong (cosℝ x ·_) (sinℝ-neg y))
    ∙ cong ((sinℝ x · cosℝ y) +_)
        (ℝRing.-DistR· (cosℝ x) (sinℝ y))


  cosℝ-sub : ∀ x y →
    cosℝ (x - y)
      ≡
    (cosℝ x · cosℝ y) + (sinℝ x · sinℝ y)
  cosℝ-sub x y =
    cosℝ-add x (- y)
    ∙ cong₂ _-_
        (cong (cosℝ x ·_) (cosℝ-neg y))
        (cong (sinℝ x ·_) (sinℝ-neg y))
    ∙ cong (λ z → (cosℝ x · cosℝ y) - z)
        (ℝRing.-DistR· (sinℝ x) (sinℝ y))
    ∙ cong ((cosℝ x · cosℝ y) +_)
        (negInvol (sinℝ x · sinℝ y))


-- Translation expansions isolate all displacement dependence in y - x.

opaque
  sinℝ-difference-expansion : ∀ x y →
    sinℝ y - sinℝ x
      ≡
    sinℝ (y - x) · cosℝ x
      + (cosℝ (y - x) - 1ℝ) · sinℝ x
  sinℝ-difference-expansion x y =
    cong (λ z → z - sinℝ x)
      (cong sinℝ (sym (subAddCancel y x))
        ∙ sinℝ-add (y - x) x)
    ∙ sym
        (addAssoc
          (sinℝ (y - x) · cosℝ x)
          (cosℝ (y - x) · sinℝ x)
          (- sinℝ x))
    ∙ cong (sinℝ (y - x) · cosℝ x +_)
        (cong
          (λ z → (cosℝ (y - x) · sinℝ x) - z)
          (sym (mulIdL (sinℝ x)))
        ∙ sym
          (ℝRing.·DistL-
            (cosℝ (y - x)) 1ℝ (sinℝ x)))


  cosℝ-difference-expansion : ∀ x y →
    cosℝ y - cosℝ x
      ≡
    (cosℝ (y - x) - 1ℝ) · cosℝ x
      - sinℝ (y - x) · sinℝ x
  cosℝ-difference-expansion x y =
    cong (λ z → z - cosℝ x)
      (cong cosℝ (sym (subAddCancel y x))
        ∙ cosℝ-add (y - x) x)
    ∙ sym
        (addAssoc
          (cosℝ (y - x) · cosℝ x)
          (- (sinℝ (y - x) · sinℝ x))
          (- cosℝ x))
    ∙ cong (cosℝ (y - x) · cosℝ x +_)
        (addComm
          (- (sinℝ (y - x) · sinℝ x))
          (- cosℝ x))
    ∙ addAssoc
        (cosℝ (y - x) · cosℝ x)
        (- cosℝ x)
        (- (sinℝ (y - x) · sinℝ x))
    ∙ cong
        (_+ (- (sinℝ (y - x) · sinℝ x)))
        (cong
          (λ z → (cosℝ (y - x) · cosℝ x) - z)
          (sym (mulIdL (cosℝ x)))
        ∙ sym
          (ℝRing.·DistL-
            (cosℝ (y - x)) 1ℝ (cosℝ x)))
