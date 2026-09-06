module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Calculus
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


opaque
  exponentialPowerSeriesTerms-nonnegative : ∀ x → 0ℝ ≤ℝ x →
    ∀ n → 0ℝ ≤ℝ powerSeriesTerms exponentialCoefficients x n
  exponentialPowerSeriesTerms-nonnegative x nonnegative n =
    subst (_≤ℝ powerSeriesTerms exponentialCoefficients x n)
      (ℝRing.0LeftAnnihilates (powℝ x n))
      (mulPres≤R-0≤ 0ℝ (exponentialCoefficients n) (powℝ x n)
        (powNonnegative x n nonnegative)
        (exponentialCoefficients-nonnegative n))

  exponentialCoefficients-one : exponentialCoefficients 1 ≡ 1ℝ
  exponentialCoefficients-one =
    sym (mulIdL (exponentialCoefficients 1))
    ∙ exponentialCoefficients-suc zero
    ∙ exponentialCoefficients-zero

  exponentialPartialSum-two : ∀ x →
    partialSum (powerSeriesTerms exponentialCoefficients x) 2 ≡ 1ℝ + x
  exponentialPartialSum-two x =
    cong₂ _+_
      (addIdL (exponentialCoefficients zero · 1ℝ)
        ∙ mulIdR (exponentialCoefficients zero)
        ∙ exponentialCoefficients-zero)
      (cong₂ _·_ exponentialCoefficients-one (mulIdR x)
        ∙ mulIdL x)

  exponentialEntireValue-linearLowerBound : ∀ x → 0ℝ ≤ℝ x →
    1ℝ + x ≤ℝ exponentialEntireValue x
  exponentialEntireValue-linearLowerBound x nonnegative =
    eventuallyLePresLimits
      {x = λ _ → 1ℝ + x}
      {y = partialSum (powerSeriesTerms exponentialCoefficients x)}
      {l = 1ℝ + x} {m = exponentialEntireValue x}
      ∣ 2 , (λ n two≤n →
        subst (_≤ℝ partialSum (powerSeriesTerms exponentialCoefficients x) n)
          (exponentialPartialSum-two x)
          (partialSumIndexMono (powerSeriesTerms exponentialCoefficients x)
            (exponentialPowerSeriesTerms-nonnegative x nonnegative)
            2 n two≤n)) ∣₁
      (constantIsLimitSequence (1ℝ + x))
      (seriesSumHasSum (powerSeriesTerms exponentialCoefficients x)
        (entirePowerSeriesSummableAt exponentialCoefficients
          exponentialPowerSeriesEntireUniformlyCauchy x))

  exponentialEntireValue-oneLowerBound : ∀ x → 0ℝ ≤ℝ x →
    1ℝ ≤ℝ exponentialEntireValue x
  exponentialEntireValue-oneLowerBound x nonnegative =
    ≤ℝ-trans 1ℝ (1ℝ + x) (exponentialEntireValue x)
      (subst (_≤ℝ 1ℝ + x) (addIdR 1ℝ)
        (addPres≤L 0ℝ x 1ℝ nonnegative))
      (exponentialEntireValue-linearLowerBound x nonnegative)

  exponentialEntireValue-positiveOnNonnegative : ∀ x → 0ℝ ≤ℝ x →
    0ℝ <ℝ exponentialEntireValue x
  exponentialEntireValue-positiveOnNonnegative x nonnegative =
    <≤ℝ-trans 0ℝ 1ℝ (exponentialEntireValue x)
      (<ℚ→<ℝ 0 1 (snd (exponentialPositiveNatural 0)))
      (exponentialEntireValue-oneLowerBound x nonnegative)
