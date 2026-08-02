module Cubical.HITs.CauchyRealsP.Analysis.Series.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute

pointwiseProduct :
  RealSequence → RealSequence → RealSequence
pointwiseProduct a b n =
  a n · b n

UniformAbsBound : ℚ₊ → RealSequence → Type
UniformAbsBound B terms =
  ∀ n →
  absℝ (terms n) ≤ℝ rat (fst B)

boundedTimesAbsoluteCauchy :
  ∀ B a b →
  UniformAbsBound B a →
  IsAbsolutelyCauchySeries b →
  IsAbsolutelyCauchySeries
    (pointwiseProduct a b)
boundedTimesAbsoluteCauchy
  B a b a-bounded b-absolute =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘ pointwiseProduct a b)
      scaledAbsoluteB
      dominates
      scaledAbsoluteBCauchy
  where
  absoluteB : RealSequence
  absoluteB =
    absℝ ∘ b

  scaledAbsoluteB : RealSequence
  scaledAbsoluteB =
    scaleSeries (rat (fst B)) absoluteB

  scaledAbsoluteBCauchy :
    IsCauchySeries scaledAbsoluteB
  scaledAbsoluteBCauchy =
    rationalScaleSeriesIsCauchy
      (fst B) absoluteB b-absolute

  dominates : ∀ n →
    absℝ
      (absℝ (pointwiseProduct a b n))
      ≤ℝ
    scaledAbsoluteB n
  dominates n =
    subst
      (_≤ℝ
        rat (fst B) · absℝ (b n))
      (sym
        ( absIdem (a n · b n)
        ∙ absMul (a n) (b n)
        ))
      (mulMonoR≤
        (absℝ (a n))
        (rat (fst B))
        (absℝ (b n))
        (absNonnegative (b n))
        (a-bounded n))

absoluteCauchyTimesBounded :
  ∀ B a b →
  IsAbsolutelyCauchySeries a →
  UniformAbsBound B b →
  IsAbsolutelyCauchySeries
    (pointwiseProduct a b)
absoluteCauchyTimesBounded
  B a b a-absolute b-bounded =
    subst
      IsAbsolutelyCauchySeries
      (funExt λ n →
        mulComm (b n) (a n))
      (boundedTimesAbsoluteCauchy
        B b a b-bounded a-absolute)

boundedTimesAbsoluteSummable :
  ∀ B a b →
  UniformAbsBound B a →
  IsAbsolutelyCauchySeries b →
  AbsolutelySummable
    (pointwiseProduct a b)
boundedTimesAbsoluteSummable
  B a b a-bounded b-absolute =
    absoluteCauchySeriesIsAbsolutelySummable
      (pointwiseProduct a b)
      (boundedTimesAbsoluteCauchy
        B a b a-bounded b-absolute)

boundedTimesSummable :
  ∀ B a b →
  UniformAbsBound B a →
  IsAbsolutelyCauchySeries b →
  Summable (pointwiseProduct a b)
boundedTimesSummable
  B a b a-bounded b-absolute =
    absoluteCauchySeriesIsSummable
      (pointwiseProduct a b)
      (boundedTimesAbsoluteCauchy
        B a b a-bounded b-absolute)
