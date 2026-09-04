module Cubical.Analysis.Real.Integration.RiemannSum.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData using (FinVec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Sampling
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.UniformContinuity


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


-- Changing only the tags changes the weighted sum by at most total width
-- times a common pointwise error bound.
riemannSumResamplingAbsBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (sample : Sampling (TaggedPartition.partition tagged))
  (f : ℝ → ℝ) (error : ℝ) →
  (∀ i →
    absℝ
      (f (TaggedPartition.tags tagged i) -
       f (Sampling.tags (TaggedPartition.partition tagged) sample i))
      ≤ℝ error) →
  absℝ
    (riemannSum tagged f -
      riemannSum (resample tagged sample) f)
    ≤ℝ (b - a) · error
riemannSumResamplingAbsBound {a} {b}
  tagged sample f error pointwise =
  subst2 _≤ℝ_
    (cong absℝ differencePath)
    totalBoundPath
    (≤ℝ-trans
      (absℝ (∑ differenceTerms))
      (∑ (λ i → absℝ (differenceTerms i)))
      (∑ errorTerms)
      (finiteSumAbsBound differenceTerms)
      (finiteSumMono
        (λ i → absℝ (differenceTerms i)) errorTerms termBound))
  where
  partition = TaggedPartition.partition tagged
  tags = TaggedPartition.tags tagged
  newTags = Sampling.tags partition sample

  differenceTerms : FinVec ℝ (Partition.intervalCount partition)
  differenceTerms i =
    width partition i · (f (tags i) - f (newTags i))

  errorTerms : FinVec ℝ (Partition.intervalCount partition)
  errorTerms i = width partition i · error

  differencePath :
    ∑ differenceTerms ≡
    riemannSum tagged f - riemannSum (resample tagged sample) f
  differencePath =
    finiteSumExt (λ i →
      ℝRing.·DistR-
        (width partition i) (f (tags i)) (f (newTags i)))
    ∙ finiteSumSub
      (λ i → width partition i · f (tags i))
      (λ i → width partition i · f (newTags i))

  termBound : ∀ i → absℝ (differenceTerms i) ≤ℝ errorTerms i
  termBound i =
    subst (_≤ℝ errorTerms i)
      (sym
        (absMul
          (width partition i) (f (tags i) - f (newTags i))
        ∙ cong (_· absℝ (f (tags i) - f (newTags i)))
            (absOfNonnegative
              (width partition i) (width-nonnegative partition i))))
      (mulPres≤L
        (absℝ (f (tags i) - f (newTags i)))
        error (width partition i)
        (0≤→isNonnegative
          (width partition i) (width-nonnegative partition i))
        (pointwise i))

  totalBoundPath : ∑ errorTerms ≡ (b - a) · error
  totalBoundPath =
    sym (finiteSumMulRight error (width partition))
    ∙ cong (_· error) (totalWidth partition)


riemannSumResamplingCloseBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (sample : Sampling (TaggedPartition.partition tagged))
  (f : ℝ → ℝ) (ε : ℚ₊) →
  (∀ i →
    f (TaggedPartition.tags tagged i) ∼[ ε ]
      f (Sampling.tags (TaggedPartition.partition tagged) sample i)) →
  absℝ
    (riemannSum tagged f -
      riemannSum (resample tagged sample) f)
    ≤ℝ (b - a) · rat (fst ε)
riemannSumResamplingCloseBound tagged sample f ε close =
  riemannSumResamplingAbsBound tagged sample f (rat (fst ε))
    (λ i → <ℝ-weaken
      (absℝ
        (f (TaggedPartition.tags tagged i) -
          f (Sampling.tags (TaggedPartition.partition tagged) sample i)))
      (rat (fst ε))
      (closeness→absDifference<
        (f (TaggedPartition.tags tagged i))
        (f (Sampling.tags (TaggedPartition.partition tagged) sample i))
        ε (close i)))


RadiuswiseRiemannResamplingBound : (ℝ → ℝ) → ℚ₊ → Type₀
RadiuswiseRiemannResamplingBound f ε =
  ∃[ δ ∈ ℚ₊ ]
    (∀ {a b} (tagged : TaggedPartition[ a , b ])
      (sample : Sampling (TaggedPartition.partition tagged)) →
      HasMeshBelow (TaggedPartition.partition tagged) δ →
      absℝ
        (riemannSum tagged f -
          riemannSum (resample tagged sample) f)
        ≤ℝ (b - a) · rat (fst ε))


radiuswiseUniformContinuityBoundsRiemannResampling : ∀ f →
  IsRadiuswiseUniformlyContinuousℝ f →
  ∀ ε → RadiuswiseRiemannResamplingBound f ε
radiuswiseUniformContinuityBoundsRiemannResampling f f-uc ε =
  PT.map
    (λ { (δ , close) →
      δ , λ tagged sample mesh →
        riemannSumResamplingCloseBound tagged sample f ε
          (close tagged sample mesh) })
    (radiuswiseUniformContinuityControlsResampling f f-uc ε)
