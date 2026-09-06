module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
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

  -- Prove the algebra with real variables before substituting series values.
  -- This keeps type checking from expanding the trigonometric definitions.
  opaque
    addMulSub : ∀ a b c → (a + b · c) - c ≡ a + (b - 1ℝ) · c
    addMulSub a b c =
      sym (addAssoc a (b · c) (- c))
      ∙ cong (a +_)
          (cong (λ z → b · c - z) (sym (mulIdL c))
          ∙ sym (ℝRing.·DistL- b 1ℝ c))

    subMulSub : ∀ a b c → (a · b - c) - b ≡ (a - 1ℝ) · b - c
    subMulSub a b c =
      sym (addAssoc (a · b) (- c) (- b))
      ∙ cong (a · b +_) (addComm (- c) (- b))
      ∙ addAssoc (a · b) (- b) (- c)
      ∙ cong (_+ (- c))
          (cong (λ z → a · b - z) (sym (mulIdL b))
          ∙ sym (ℝRing.·DistL- a 1ℝ b))


-- Subtraction formulas are immediate consequences of the total addition
-- laws and parity.  Keeping them named avoids repeating ring normalization
-- in later estimates.
-- Spell x - y as x + (- y) under sinℝ and cosℝ to match the addition
-- theorem syntactically without expanding the completed series values.

opaque
  sinℝ-sub : ∀ x y →
    sinℝ (x + (- y))
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
    cosℝ (x + (- y))
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
    ∙ addMulSub
        (sinℝ (y - x) · cosℝ x) (cosℝ (y - x)) (sinℝ x)


  cosℝ-difference-expansion : ∀ x y →
    cosℝ y - cosℝ x
      ≡
    (cosℝ (y - x) - 1ℝ) · cosℝ x
      - sinℝ (y - x) · sinℝ x
  cosℝ-difference-expansion x y =
    cong (λ z → z - cosℝ x)
      (cong cosℝ (sym (subAddCancel y x))
        ∙ cosℝ-add (y - x) x)
    ∙ subMulSub
        (cosℝ (y - x)) (cosℝ x) (sinℝ (y - x) · sinℝ x)
