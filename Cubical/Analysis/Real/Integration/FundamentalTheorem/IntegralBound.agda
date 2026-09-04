module Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegralBound where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


-- A pointwise absolute bound passes to every tagged Riemann sum.  The
-- nonnegative cell widths are the only sign information needed here.

riemannSum-absBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (f : ℝ → ℝ) (bound : ℝ) →
  (∀ x → absℝ (f x) ≤ℝ bound) →
  absℝ (riemannSum tagged f) ≤ℝ (b - a) · bound
riemannSum-absBound {a} {b} tagged f bound pointwise =
  subst (absℝ (riemannSum tagged f) ≤ℝ_)
    (cong (_· bound) (totalWidth partition))
    (finiteSumWeightedAbsBound
      (width partition) (λ i → f (tags i)) bound
      (width-nonnegative partition) (λ i → pointwise (tags i)))
  where
  partition = TaggedPartition.partition tagged
  tags = TaggedPartition.tags tagged


-- This is the semantic Riemann-integral analogue of the usual
-- |integral f| ≤ (b-a)B estimate.  The finite bound passes to the limit
-- along dyadic partitions by continuity of absolute value and closed order.

riemannIntegral-absBound : ∀ a b → a ≤ℝ b →
  ∀ f value bound →
  HasRiemannIntegralOn f a b value →
  (∀ x → absℝ (f x) ≤ℝ bound) →
  absℝ value ≤ℝ (b - a) · bound
riemannIntegral-absBound a b a≤b f value bound hasIntegral pointwise =
  pointwiseLePresLimits
    {x = λ n → absℝ (riemannSum (partitions n) f)}
    {y = λ _ → (b - a) · bound}
    {l = absℝ value} {m = (b - a) · bound}
    (λ n → riemannSum-absBound (partitions n) f bound pointwise)
    (continuousPreservesIsLimitSequence absℝ abs-isContinuous
      {x = λ n → riemannSum (partitions n) f} {l = value}
      (riemannSumsConverge f value partitions
        (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b)
        hasIntegral))
    (constantIsLimitSequence ((b - a) · bound))
  where
  partitions = dyadicLeftTaggedPartition a b a≤b
