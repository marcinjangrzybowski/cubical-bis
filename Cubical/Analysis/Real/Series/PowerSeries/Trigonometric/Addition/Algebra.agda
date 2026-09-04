module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


-- A six-factor rearrangement used by both trigonometric product summands.
-- It is kept explicit so the finite addition proof does not depend on a
-- normalization tactic.

rearrangeSixFactors : ∀ a b c d x y →
  ((a · c) · x) · ((b · d) · y)
    ≡ (a · b) · ((c · x) · (d · y))
rearrangeSixFactors a b c d x y =
  interchange (a · c) x (b · d) y
  ∙ cong (_· (x · y)) (interchange a c b d)
  ∙ sym (mulAssoc (a · b) (c · d) (x · y))
  ∙ cong ((a · b) ·_) (interchange c d x y)
  where
  interchange : ∀ p q r s →
    (p · q) · (r · s) ≡ (p · r) · (q · s)
  interchange p q r s =
    sym (mulAssoc p q (r · s))
    ∙ cong (p ·_) (mulAssoc q r s)
    ∙ cong (λ z → p · (z · s)) (mulComm q r)
    ∙ cong (p ·_) (sym (mulAssoc r q s))
    ∙ mulAssoc p r (q · s)


combine-sine-products :
  ∀ sine-left cosine-left sine-right cosine-right
    left-coefficient left-power right-coefficient right-power →
  (((sine-left · left-coefficient) · left-power) ·
      ((cosine-right · right-coefficient) · right-power))
    +
  (((cosine-left · left-coefficient) · left-power) ·
      ((sine-right · right-coefficient) · right-power))
    ≡
  (sine-left · cosine-right + cosine-left · sine-right) ·
    ((left-coefficient · left-power) ·
      (right-coefficient · right-power))
combine-sine-products
    sine-left cosine-left sine-right cosine-right
    left-coefficient left-power right-coefficient right-power =
  cong₂ _+_
    (rearrangeSixFactors
      sine-left cosine-right left-coefficient right-coefficient
      left-power right-power)
    (rearrangeSixFactors
      cosine-left sine-right left-coefficient right-coefficient
      left-power right-power)
  ∙ sym
      (mulDistL
        (sine-left · cosine-right)
        (cosine-left · sine-right)
        magnitude)
  where
  magnitude =
    (left-coefficient · left-power) ·
      (right-coefficient · right-power)


combine-cosine-products :
  ∀ sine-left cosine-left sine-right cosine-right
    left-coefficient left-power right-coefficient right-power →
  (((cosine-left · left-coefficient) · left-power) ·
      ((cosine-right · right-coefficient) · right-power))
    +
  - (((sine-left · left-coefficient) · left-power) ·
      ((sine-right · right-coefficient) · right-power))
    ≡
  (cosine-left · cosine-right + - (sine-left · sine-right)) ·
    ((left-coefficient · left-power) ·
      (right-coefficient · right-power))
combine-cosine-products
    sine-left cosine-left sine-right cosine-right
    left-coefficient left-power right-coefficient right-power =
  cong₂ _+_
    (rearrangeSixFactors
      cosine-left cosine-right left-coefficient right-coefficient
      left-power right-power)
    (cong -_
      (rearrangeSixFactors
        sine-left sine-right left-coefficient right-coefficient
        left-power right-power))
  ∙ cong
      ((cosine-left · cosine-right) · magnitude +_)
      (sym (ℝRing.-DistL· (sine-left · sine-right) magnitude))
  ∙ sym
      (mulDistL
        (cosine-left · cosine-right)
        (- (sine-left · sine-right))
        magnitude)
  where
  magnitude =
    (left-coefficient · left-power) ·
      (right-coefficient · right-power)
