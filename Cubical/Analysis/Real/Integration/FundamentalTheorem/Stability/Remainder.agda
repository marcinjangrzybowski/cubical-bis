module Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability.Remainder where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

opaque
  uniformDerivativeRemainderTransferBound : ∀ (increment approximation slope approximateSlope step error remainder : ℝ) →
    absℝ (increment - approximation) ≤ℝ error · absℝ step →
    absℝ (slope - approximateSlope) ≤ℝ error →
    absℝ (approximation - approximateSlope · step) ≤ℝ remainder · absℝ step →
    absℝ (increment - slope · step) ≤ℝ ((error + error) + remainder) · absℝ step
  uniformDerivativeRemainderTransferBound increment approximation slope approximateSlope step error remainder
      incrementsClose slopesClose approximationBound =
    subst (absℝ (increment - slope · step) ≤ℝ_)
      (cong (_+ remainder · absℝ step) (sym (mulDistL error error (absℝ step)))
        ∙ sym (mulDistL (error + error) remainder (absℝ step)))
      (subst (_≤ℝ (error · absℝ step + error · absℝ step) + remainder · absℝ step)
        (sym (cong absℝ errorPath))
        (≤ℝ-trans (absℝ (difference + (approximation - approximateSlope · step)))
          (absℝ difference + absℝ (approximation - approximateSlope · step))
          ((error · absℝ step + error · absℝ step) + remainder · absℝ step)
          (absTriangle difference (approximation - approximateSlope · step))
          (addPres≤ (absℝ difference) (error · absℝ step + error · absℝ step)
            (absℝ (approximation - approximateSlope · step)) (remainder · absℝ step)
            (≤ℝ-trans (absℝ difference)
              (absℝ (increment - approximation) + absℝ ((slope - approximateSlope) · step))
              (error · absℝ step + error · absℝ step)
              (absSubTriangle (increment - approximation) ((slope - approximateSlope) · step))
              (addPres≤ (absℝ (increment - approximation)) (error · absℝ step)
                (absℝ ((slope - approximateSlope) · step)) (error · absℝ step) incrementsClose
                (subst (_≤ℝ error · absℝ step) (sym (absMul (slope - approximateSlope) step))
                  (mulPres≤R-0≤ (absℝ (slope - approximateSlope)) error (absℝ step)
                    (absNonnegative step) slopesClose)))) approximationBound)))
    where
    difference : ℝ
    difference = (increment - approximation) - (slope - approximateSlope) · step
    errorPath : increment - slope · step ≡ difference + (approximation - approximateSlope · step)
    errorPath = sym (subAddCancel (increment - slope · step) (approximation - approximateSlope · step))
      ∙ cong (_+ (approximation - approximateSlope · step))
        (differenceOfDifferences increment (slope · step) approximation (approximateSlope · step)
          ∙ cong (λ z → (increment - approximation) - z) (sym (ℝRing.·DistL- slope approximateSlope step)))

