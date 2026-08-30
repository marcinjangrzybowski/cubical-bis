module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.FinData using (Fin ; FinVec)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (neg-sub)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
  using (≤ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (bounds→abs≤)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
  using (add-preserves≤-right ; add-preserves≤-left)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
  using (neg-reverses≤)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (scalar-preserves≤ ; rationalHalfNonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; isProp<ℝ ; ≤<ℝ-trans ; ≪≤ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition


-- A pointwise mesh predicate is enough for all error estimates.  Keeping the
-- bound pointwise avoids choosing a maximum vertex width and works uniformly
-- for empty and degenerate partitions.

HasMeshBelow : ∀ {a b} →
  Partition[ a , b ] → ℚ₊ → Type₀
HasMeshBelow partition δ =
  ∀ i → width partition i <ℝ Real.ιℚ (fst δ)


isPropHasMeshBelow : ∀ {a b}
  (partition : Partition[ a , b ]) δ →
  isProp (HasMeshBelow partition δ)
isPropHasMeshBelow partition δ =
  isPropΠ λ i → isProp<ℝ
    (width partition i) (Real.ιℚ (fst δ))


meshBelowMonotone : ∀ {a b}
  (partition : Partition[ a , b ]) δ ε →
  δ ≤₊ ε →
  HasMeshBelow partition δ →
  HasMeshBelow partition ε
meshBelowMonotone partition δ ε δ≤ε mesh i =
  ≪≤ℝ-trans
    (width partition i)
    (Real.ιℚ (fst δ))
    (Real.ιℚ (fst ε))
    (mesh i)
    (≤ℚ→≤ℝ (fst δ) (fst ε) δ≤ε)


-- A partition scheme becomes fine one requested radius at a time.  The tail
-- index remains truncated, matching the native Cauchy-sequence interface.

HasVanishingMesh : ∀ {a b} →
  (ℕ → TaggedPartition[ a , b ]) → Type₀
HasVanishingMesh partitions =
  ∀ δ →
    ∃[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        HasMeshBelow
          (TaggedPartition[_,_].partition (partitions n)) δ)


isPropHasVanishingMesh : ∀ {a b}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  isProp (HasVanishingMesh partitions)
isPropHasVanishingMesh partitions =
  isPropΠ λ _ → squash₁


-- Two points in one subinterval are at most its width apart.  This lemma is
-- independent of partitions and will also be useful for interval estimates.

pointsInIntervalDistanceBound : ∀ lower upper x y →
  lower ≤ℝ x → x ≤ℝ upper →
  lower ≤ℝ y → y ≤ℝ upper →
  Abs.absℝ (x Group.- y) ≤ℝ upper Group.- lower
pointsInIntervalDistanceBound
  lower upper x y lower≤x x≤upper lower≤y y≤upper =
  bounds→abs≤ (x Group.- y) (upper Group.- lower)
    (≤ℝ-trans
      (x Group.- y) (upper Group.- y) (upper Group.- lower)
      (add-preserves≤-right x upper (Neg.- y) x≤upper)
        (add-preserves≤-left
          (Neg.- y) (Neg.- lower) upper
          (neg-reverses≤ lower y lower≤y)))
    (subst (_≤ℝ upper Group.- lower)
      (sym (neg-sub x y))
      (≤ℝ-trans
        (y Group.- x) (upper Group.- x) (upper Group.- lower)
        (add-preserves≤-right y upper (Neg.- x) y≤upper)
          (add-preserves≤-left
            (Neg.- x) (Neg.- lower) upper
            (neg-reverses≤ lower x lower≤x))))


-- Resampling keeps all vertices fixed and changes only the chosen tags.

record Sampling {a b} (partition : Partition[ a , b ]) : Type₀ where
  field
    tags : FinVec Real.ℝ (Partition[_,_].intervalCount partition)
    lower≤tag :
      (i : Fin (Partition[_,_].intervalCount partition)) →
      Partition[_,_].points partition
        (Cubical.Data.FinData.weakenFin i) ≤ℝ tags i
    tag≤upper :
      (i : Fin (Partition[_,_].intervalCount partition)) →
      tags i ≤ℝ Partition[_,_].points partition
        (Cubical.Data.FinData.suc i)


samplingToTaggedPartition : ∀ {a b}
  (partition : Partition[ a , b ]) →
  Sampling partition →
  TaggedPartition[ a , b ]
samplingToTaggedPartition partition sample
  .TaggedPartition[_,_].partition = partition
samplingToTaggedPartition partition sample
  .TaggedPartition[_,_].tags = Sampling.tags sample
samplingToTaggedPartition partition sample
  .TaggedPartition[_,_].lower≤tag = Sampling.lower≤tag sample
samplingToTaggedPartition partition sample
  .TaggedPartition[_,_].tag≤upper = Sampling.tag≤upper sample


leftSampling : ∀ {a b} (partition : Partition[ a , b ]) →
  Sampling partition
leftSampling partition .Sampling.tags i =
  Partition[_,_].points partition
    (Cubical.Data.FinData.weakenFin i)
leftSampling partition .Sampling.lower≤tag i =
  ≤ℝ-refl _
leftSampling partition .Sampling.tag≤upper i =
  Partition[_,_].monotone partition i


rightSampling : ∀ {a b} (partition : Partition[ a , b ]) →
  Sampling partition
rightSampling partition .Sampling.tags i =
  Partition[_,_].points partition
    (Cubical.Data.FinData.suc i)
rightSampling partition .Sampling.lower≤tag i =
  Partition[_,_].monotone partition i
rightSampling partition .Sampling.tag≤upper i =
  ≤ℝ-refl _


-- The midpoint sampler is defined once for arbitrary partitions.  Keeping it
-- at the `Sampling` layer lets equal, dyadic, and future adaptive partition
-- families reuse both the construction and all resampling estimates.

midpoint : Real.ℝ → Real.ℝ → Real.ℝ
midpoint x y = rationalHalf Scalar.⋆ (x Add.+ y)


private
  half-double : ∀ x → midpoint x x ≡ x
  half-double x =
    scalar-dist-right rationalHalf x x
    ∙ sym (scalar-dist-left rationalHalf rationalHalf x)
    ∙ cong (Scalar._⋆ x) ℚ!
    ∙ scalar-id x


midpoint-lower : ∀ x y → x ≤ℝ y → x ≤ℝ midpoint x y
midpoint-lower x y x≤y =
  subst (λ z → z ≤ℝ midpoint x y) (half-double x)
    (scalar-preserves≤ rationalHalf rationalHalfNonnegative
      (x Add.+ x) (x Add.+ y)
      (add-preserves≤-left x y x x≤y))


midpoint-upper : ∀ x y → x ≤ℝ y → midpoint x y ≤ℝ y
midpoint-upper x y x≤y =
  subst (midpoint x y ≤ℝ_) (half-double y)
    (scalar-preserves≤ rationalHalf rationalHalfNonnegative
      (x Add.+ y) (y Add.+ y)
      (add-preserves≤-right x y y x≤y))


midpointSampling : ∀ {a b} (partition : Partition[ a , b ]) →
  Sampling partition
midpointSampling partition .Sampling.tags i =
  midpoint
    (Partition[_,_].points partition
      (Cubical.Data.FinData.weakenFin i))
    (Partition[_,_].points partition
      (Cubical.Data.FinData.suc i))
midpointSampling partition .Sampling.lower≤tag i =
  midpoint-lower
    (Partition[_,_].points partition
      (Cubical.Data.FinData.weakenFin i))
    (Partition[_,_].points partition
      (Cubical.Data.FinData.suc i))
    (Partition[_,_].monotone partition i)
midpointSampling partition .Sampling.tag≤upper i =
  midpoint-upper
    (Partition[_,_].points partition
      (Cubical.Data.FinData.weakenFin i))
    (Partition[_,_].points partition
      (Cubical.Data.FinData.suc i))
    (Partition[_,_].monotone partition i)


leftTaggedPartition : ∀ {a b} →
  Partition[ a , b ] → TaggedPartition[ a , b ]
leftTaggedPartition partition =
  samplingToTaggedPartition partition (leftSampling partition)


rightTaggedPartition : ∀ {a b} →
  Partition[ a , b ] → TaggedPartition[ a , b ]
rightTaggedPartition partition =
  samplingToTaggedPartition partition (rightSampling partition)


midpointTaggedPartition : ∀ {a b} →
  Partition[ a , b ] → TaggedPartition[ a , b ]
midpointTaggedPartition partition =
  samplingToTaggedPartition partition (midpointSampling partition)


taggedSampling : ∀ {a b} (tagged : TaggedPartition[ a , b ]) →
  Sampling (TaggedPartition[_,_].partition tagged)
taggedSampling tagged .Sampling.tags =
  TaggedPartition[_,_].tags tagged
taggedSampling tagged .Sampling.lower≤tag =
  TaggedPartition[_,_].lower≤tag tagged
taggedSampling tagged .Sampling.tag≤upper =
  TaggedPartition[_,_].tag≤upper tagged


resample : ∀ {a b}
  (tagged : TaggedPartition[ a , b ]) →
  Sampling (TaggedPartition[_,_].partition tagged) →
  TaggedPartition[ a , b ]
resample tagged sample .TaggedPartition[_,_].partition =
  TaggedPartition[_,_].partition tagged
resample tagged sample .TaggedPartition[_,_].tags =
  Sampling.tags sample
resample tagged sample .TaggedPartition[_,_].lower≤tag =
  Sampling.lower≤tag sample
resample tagged sample .TaggedPartition[_,_].tag≤upper =
  Sampling.tag≤upper sample


resampledTagsClose : ∀ {a b}
  (tagged : TaggedPartition[ a , b ]) δ
  (sample : Sampling (TaggedPartition[_,_].partition tagged)) →
  HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
  ∀ i →
  TaggedPartition[_,_].tags tagged i
    Real.Base.≈ᶜ[ δ ] Sampling.tags sample i
resampledTagsClose tagged δ sample mesh i =
  absDifference<→closeness
    (TaggedPartition[_,_].tags tagged i)
    (Sampling.tags sample i) δ
    (≤<ℝ-trans
      (Abs.absℝ
        (TaggedPartition[_,_].tags tagged i Group.-
          Sampling.tags sample i))
      (width (TaggedPartition[_,_].partition tagged) i)
      (Real.ιℚ (fst δ))
      (pointsInIntervalDistanceBound
        (Partition[_,_].points
          (TaggedPartition[_,_].partition tagged)
          (Cubical.Data.FinData.weakenFin i))
        (Partition[_,_].points
          (TaggedPartition[_,_].partition tagged)
          (Cubical.Data.FinData.suc i))
        (TaggedPartition[_,_].tags tagged i)
        (Sampling.tags sample i)
        (TaggedPartition[_,_].lower≤tag tagged i)
        (TaggedPartition[_,_].tag≤upper tagged i)
        (Sampling.lower≤tag sample i)
        (Sampling.tag≤upper sample i))
      (mesh i))


-- Radiuswise uniform continuity therefore controls every legal resampling of
-- every sufficiently fine partition.  The controlling mesh radius remains
-- under truncation at the requested output radius.

RadiuswiseResamplingControl : (Real.ℝ → Real.ℝ) → ℚ₊ → Type₀
RadiuswiseResamplingControl f ε =
  ∃[ δ ∈ ℚ₊ ]
    (∀ {a b} (tagged : TaggedPartition[ a , b ])
      (sample : Sampling (TaggedPartition[_,_].partition tagged)) →
      HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
      ∀ i →
      f (TaggedPartition[_,_].tags tagged i)
        Real.Base.≈ᶜ[ ε ] f (Sampling.tags sample i))


radiuswiseUniformContinuityControlsResampling : ∀ f →
  IsRadiuswiseUniformlyContinuousℝ f →
  ∀ ε → RadiuswiseResamplingControl f ε
radiuswiseUniformContinuityControlsResampling f f-uc ε =
  PT.map
    (λ { (δ , close) →
      δ , λ tagged sample mesh i →
        close _ _
          (resampledTagsClose
            tagged δ sample mesh i) })
    (f-uc ε)
