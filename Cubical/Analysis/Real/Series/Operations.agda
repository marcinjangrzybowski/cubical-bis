module Cubical.Analysis.Real.Series.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (zero; suc)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


scaleSeries : ℝ → RealSequence → RealSequence
scaleSeries c terms n = c · terms n


partialSum-scale : ∀ c terms n →
  partialSum (scaleSeries c terms) n ≡
  c · partialSum terms n
partialSum-scale c terms zero =
  sym (ℝRing.0RightAnnihilates c)
partialSum-scale c terms (suc n) =
  cong (_+ (c · terms n))
    (partialSum-scale c terms n)
  ∙ sym (mulDistR c (partialSum terms n) (terms n))


scaleHasSum : ∀ c terms value →
  HasSum terms value →
  HasSum (scaleSeries c terms) (c · value)
scaleHasSum c terms value terms-sum =
  subst
    (λ sequence → isLimitSequence sequence (c · value))
    (funExt λ n → sym (partialSum-scale c terms n))
    (mulPresIsLimitSequence
      (constantIsLimitSequence c)
      terms-sum)


scaleSummable : ∀ c terms →
  Summable terms → Summable (scaleSeries c terms)
scaleSummable c terms summable =
  c · seriesSum terms summable
  , scaleHasSum
      c terms (seriesSum terms summable)
      (seriesSumHasSum terms summable)


seriesSum-scale : ∀ c terms
  (summable : Summable terms)
  (scaled-summable : Summable (scaleSeries c terms)) →
  seriesSum (scaleSeries c terms) scaled-summable ≡
  c · seriesSum terms summable
seriesSum-scale c terms summable scaled-summable =
  seriesSumIndependent
    (scaleSeries c terms) scaled-summable
    (scaleSummable c terms summable)
