module Cubical.Analysis.Real.Integration.RiemannIntegral.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegralBound

private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
open ℝSum using (∑)

opaque
  riemannSum-monoOn : ∀ {a b} (tagged : TaggedPartition[ a , b ]) f g →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≤ℝ g x) →
    riemannSum tagged f ≤ℝ riemannSum tagged g
  riemannSum-monoOn {a} {b} tagged f g pointwise =
    finiteSumMono (λ i → width p i · f (tags i)) (λ i → width p i · g (tags i))
      (λ i → mulPres≤L (f (tags i)) (g (tags i)) (width p i)
        (0≤→isNonnegative (width p i) (width-nonnegative p i))
        (pointwise (tags i)
          (≤ℝ-trans a (Partition.points p (FD.weakenFin i)) (tags i)
            (partitionPointLowerBound p (FD.weakenFin i)) (TaggedPartition.lower≤tag tagged i))
          (≤ℝ-trans (tags i) (Partition.points p (FD.suc i)) b
            (TaggedPartition.tag≤upper tagged i) (partitionPointUpperBound p (FD.suc i)))))
    where
    p : Partition[ a , b ]
    p = TaggedPartition.partition tagged
    tags : Fin (Partition.intervalCount p) → ℝ
    tags = TaggedPartition.tags tagged

  riemannIntegral-monoOn : ∀ a b → a ≤ℝ b → ∀ f g value value' →
    HasRiemannIntegralOn f a b value → HasRiemannIntegralOn g a b value' →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≤ℝ g x) → value ≤ℝ value'
  riemannIntegral-monoOn a b a≤b f g value value' hasValue hasValue' pointwise =
    pointwiseLePresLimits
      {x = λ n → riemannSum (dyadicLeftTaggedPartition a b a≤b n) f}
      {y = λ n → riemannSum (dyadicLeftTaggedPartition a b a≤b n) g}
      {l = value} {m = value'}
      (λ n → riemannSum-monoOn (dyadicLeftTaggedPartition a b a≤b n) f g pointwise)
      (riemannSumsConverge f value (dyadicLeftTaggedPartition a b a≤b)
        (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b) hasValue)
      (riemannSumsConverge g value' (dyadicLeftTaggedPartition a b a≤b)
        (dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b) hasValue')

  riemannIntegral-nonnegativeOn : ∀ a b → a ≤ℝ b → ∀ f value →
    HasRiemannIntegralOn f a b value →
    (∀ x → a ≤ℝ x → x ≤ℝ b → 0ℝ ≤ℝ f x) → 0ℝ ≤ℝ value
  riemannIntegral-nonnegativeOn a b a≤b f value hasValue pointwise =
    subst (_≤ℝ value) (ℝRing.0RightAnnihilates (b - a))
      (riemannIntegral-monoOn a b a≤b (λ _ → 0ℝ) f ((b - a) · 0ℝ) value
        (constantHasRiemannIntegral a b 0ℝ) hasValue pointwise)

  riemannIntegral-lowerBoundOn : ∀ a b → a ≤ℝ b → ∀ f value lower →
    HasRiemannIntegralOn f a b value →
    (∀ x → a ≤ℝ x → x ≤ℝ b → lower ≤ℝ f x) → (b - a) · lower ≤ℝ value
  riemannIntegral-lowerBoundOn a b a≤b f value lower hasValue =
    riemannIntegral-monoOn a b a≤b (λ _ → lower) f ((b - a) · lower) value
      (constantHasRiemannIntegral a b lower) hasValue

  riemannIntegral-upperBoundOn : ∀ a b → a ≤ℝ b → ∀ f value upper →
    HasRiemannIntegralOn f a b value →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≤ℝ upper) → value ≤ℝ (b - a) · upper
  riemannIntegral-upperBoundOn a b a≤b f value upper hasValue =
    riemannIntegral-monoOn a b a≤b f (λ _ → upper) value ((b - a) · upper)
      hasValue (constantHasRiemannIntegral a b upper)

  riemannSum-differenceBoundOn : ∀ {a b} (tagged : TaggedPartition[ a , b ]) f g error →
    (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x - g x) ≤ℝ error) →
    absℝ (riemannSum tagged f - riemannSum tagged g) ≤ℝ (b - a) · error
  riemannSum-differenceBoundOn {a} {b} tagged f g error pointwise =
    subst (λ value → absℝ value ≤ℝ (b - a) · error) (riemannSum-sub tagged f g)
      (riemannSum-absBoundOn tagged (λ x → f x - g x) error pointwise)

  riemannIntegral-differenceBoundOn : ∀ a b → a ≤ℝ b → ∀ f g value value' error →
    HasRiemannIntegralOn f a b value → HasRiemannIntegralOn g a b value' →
    (∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x - g x) ≤ℝ error) →
    absℝ (value - value') ≤ℝ (b - a) · error
  riemannIntegral-differenceBoundOn a b a≤b f g value value' error hasValue hasValue' =
    riemannIntegral-absBoundOn a b a≤b (λ x → f x - g x) (value - value') error
      (subHasRiemannIntegral f g value value' hasValue hasValue')
