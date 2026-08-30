module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (FinVec)
open import Cubical.Data.Sigma
import Cubical.Data.FinData as FD
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (add-monotone ; abs-triangle)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; nonnegative→abs-self ; mul-preserves≤-left-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (<ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference<)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  zeroℝ : Real.ℝ
  zeroℝ = CommRingStr.0r (snd ℝCommRing)

open ℝSum using
  (∑ ; ∑Ext ; ∑Split- ; ∑Mulldist)


-- The finite triangle inequality is stated for arbitrary pointwise bounds.
-- It is independent of integration and avoids importing the series partial-
-- sum convention merely to reason about a `FinVec` sum.

finiteSumAbsBound : ∀ {n}
  (values bounds : FinVec Real.ℝ n) →
  (∀ i → Abs.absℝ (values i) ≤ℝ bounds i) →
  Abs.absℝ (∑ values) ≤ℝ ∑ bounds
finiteSumAbsBound {n = zero} values bounds pointwise =
  subst (_≤ℝ zeroℝ)
    (sym Abs.absℝ-zero)
    (≤ℝ-refl zeroℝ)
finiteSumAbsBound {n = suc n} values bounds pointwise =
  ≤ℝ-trans
    (Abs.absℝ (values FD.zero Add.+ ∑ (λ i → values (FD.suc i))))
    (Abs.absℝ (values FD.zero) Add.+
      Abs.absℝ (∑ (λ i → values (FD.suc i))))
    (bounds FD.zero Add.+ ∑ (λ i → bounds (FD.suc i)))
    (abs-triangle (values FD.zero) (∑ (λ i → values (FD.suc i))))
    (add-monotone
      (Abs.absℝ (values FD.zero)) (bounds FD.zero)
      (Abs.absℝ (∑ (λ i → values (FD.suc i))))
      (∑ (λ i → bounds (FD.suc i)))
      (pointwise FD.zero)
      (finiteSumAbsBound
        (λ i → values (FD.suc i)) (λ i → bounds (FD.suc i))
        (λ i → pointwise (FD.suc i))))


-- If two samplings use the same vertices and their values differ by at most
-- `error`, their Riemann sums differ by at most interval-width times `error`.
-- This is the central weighted resampling estimate.

riemannSumResamplingAbsBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (sample : Sampling (TaggedPartition[_,_].partition tagged))
  (f : Real.ℝ → Real.ℝ) (error : Real.ℝ) →
  (∀ i →
    Abs.absℝ
      (f (TaggedPartition[_,_].tags tagged i) Group.-
       f (Sampling.tags sample i)) ≤ℝ error) →
  Abs.absℝ
    (riemannSum tagged f Group.- riemannSum (resample tagged sample) f)
    ≤ℝ
  (b Group.- a) Mul.· error
riemannSumResamplingAbsBound {a} {b} tagged sample f error pointwise =
  subst2 _≤ℝ_
    (cong Abs.absℝ differencePath)
    totalBoundPath
    (finiteSumAbsBound differenceTerms errorTerms termBound)
  where
  partition = TaggedPartition[_,_].partition tagged
  tags = TaggedPartition[_,_].tags tagged
  newTags = Sampling.tags sample

  differenceTerms : FinVec Real.ℝ
    (Partition[_,_].intervalCount partition)
  differenceTerms i =
    width partition i Mul.· (f (tags i) Group.- f (newTags i))

  errorTerms : FinVec Real.ℝ
    (Partition[_,_].intervalCount partition)
  errorTerms i = width partition i Mul.· error

  differencePath :
    ∑ differenceTerms ≡
    riemannSum tagged f Group.- riemannSum (resample tagged sample) f
  differencePath =
    ∑Ext (λ i →
      ℝRing.·DistR- (width partition i) (f (tags i)) (f (newTags i)))
    ∙ ∑Split-
      (λ i → width partition i Mul.· f (tags i))
      (λ i → width partition i Mul.· f (newTags i))

  termBound : ∀ i →
    Abs.absℝ (differenceTerms i) ≤ℝ errorTerms i
  termBound i =
    subst (λ z → z ≤ℝ errorTerms i)
      (sym
        (abs-mul
          (width partition i)
          (f (tags i) Group.- f (newTags i))
        ∙ cong (Mul._·
            Abs.absℝ (f (tags i) Group.- f (newTags i)))
            (nonnegative→abs-self
              (width partition i)
              (width-nonnegative partition i))))
      (mul-preserves≤-left-nonnegative
        (Abs.absℝ (f (tags i) Group.- f (newTags i)))
        error (width partition i)
        (pointwise i)
        (width-nonnegative partition i))

  totalBoundPath :
    ∑ errorTerms ≡ (b Group.- a) Mul.· error
  totalBoundPath =
    sym (∑Mulldist error (width partition))
    ∙ cong (Mul._· error) (totalWidth partition)


riemannSumResamplingCloseBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (sample : Sampling (TaggedPartition[_,_].partition tagged))
  (f : Real.ℝ → Real.ℝ) (ε : ℚ₊) →
  (∀ i →
    f (TaggedPartition[_,_].tags tagged i)
      Real.Base.≈ᶜ[ ε ] f (Sampling.tags sample i)) →
  Abs.absℝ
    (riemannSum tagged f Group.- riemannSum (resample tagged sample) f)
    ≤ℝ
  (b Group.- a) Mul.· Real.ιℚ (fst ε)
riemannSumResamplingCloseBound tagged sample f ε close =
  riemannSumResamplingAbsBound tagged sample f (Real.ιℚ (fst ε))
    (λ i → <ℝ-weaken _ _
      (closeness→absDifference< _ _ ε (close i)))


-- This is the Riemann-sum form of radiuswise uniform continuity.  Notice
-- that the mesh radius remains below propositional truncation: consumers can
-- eliminate it directly into a proposition such as a Cauchy-tail estimate,
-- but cannot silently assemble a global modulus.

RadiuswiseRiemannResamplingBound :
  (Real.ℝ → Real.ℝ) → ℚ₊ → Type₀
RadiuswiseRiemannResamplingBound f ε =
  ∃[ δ ∈ ℚ₊ ]
    (∀ {a b} (tagged : TaggedPartition[ a , b ])
      (sample : Sampling (TaggedPartition[_,_].partition tagged)) →
      HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
      Abs.absℝ
        (riemannSum tagged f Group.-
          riemannSum (resample tagged sample) f)
        ≤ℝ
      (b Group.- a) Mul.· Real.ιℚ (fst ε))


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
