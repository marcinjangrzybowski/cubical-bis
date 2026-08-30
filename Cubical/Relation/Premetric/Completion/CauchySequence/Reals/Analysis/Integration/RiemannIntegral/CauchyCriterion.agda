module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.CauchyCriterion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ ; max)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Sequential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral


-- This is the Cauchy criterion for Riemann integration.  Its radius remains
-- under truncation separately for each requested error, just as in
-- `IsRiemannIntegral`; no modulus of integrability is selected.

IsRiemannCauchy : ∀ {a b} → (Real.ℝ → Real.ℝ) → Type₀
IsRiemannCauchy {a} {b} f =
  ∀ ε →
    ∃[ δ ∈ ℚ₊ ]
      (∀ (left right : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition left) δ →
        HasMeshBelow (TaggedPartition[_,_].partition right) δ →
        riemannSum left f Real.Base.≈ᶜ[ ε ] riemannSum right f)


isPropIsRiemannCauchy : ∀ {a b} f →
  isProp (IsRiemannCauchy {a} {b} f)
isPropIsRiemannCauchy f = isPropΠ λ _ → squash₁


-- Any one vanishing-mesh family samples the Cauchy filter of all fine sums.

riemannCauchyGivesCauchyQuadrature : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  IsRiemannCauchy f →
  CauchyQuadrature a b f
riemannCauchyGivesCauchyQuadrature {a} {b} {f = f}
  partitions mesh→0 stable
  .CauchyQuadrature.partitions = partitions
riemannCauchyGivesCauchyQuadrature {a} {b} {f = f}
  partitions mesh→0 stable
  .CauchyQuadrature.sumsCauchy ε =
  PT.rec squash₁ use-stability-radius (stable ε)
  where
  use-stability-radius :
    Σ[ δ ∈ ℚ₊ ]
      (∀ (left right : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition left) δ →
        HasMeshBelow (TaggedPartition[_,_].partition right) δ →
        riemannSum left f Real.Base.≈ᶜ[ ε ] riemannSum right f) →
    ∥ CauchyTail (quadratureSequence partitions f) ε ∥₁
  use-stability-radius (δ , compare) =
    PT.map
      (λ { (N , fine) →
        N , λ m n N≤m N≤n →
          compare (partitions m) (partitions n)
            (fine m N≤m) (fine n N≤n) })
      (mesh→0 δ)


-- Completeness now supplies a value.  Pairwise stability compares an
-- arbitrary fine sum to a sufficiently late scheme sum, while convergence
-- compares that scheme sum to the completed value.  The two finite choices
-- are combined with `max`; they are never assembled across all radii.

riemannCauchyLimitIsRiemannIntegral : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ])
  (mesh→0 : HasVanishingMesh partitions)
  (stable : IsRiemannCauchy f) →
  IsRiemannIntegral {a} {b} f
    (quadratureValue
      (riemannCauchyGivesCauchyQuadrature
        {a = a} {b = b} {f = f} partitions mesh→0 stable))
riemannCauchyLimitIsRiemannIntegral {a} {b} {f = f}
  partitions mesh→0 stable ε =
  PT.rec squash₁ use-stability-radius (stable (ε /2₊))
  where
  q : CauchyQuadrature a b f
  q = riemannCauchyGivesCauchyQuadrature
    {a = a} {b = b} {f = f} partitions mesh→0 stable

  use-stability-radius :
    Σ[ δ ∈ ℚ₊ ]
      (∀ (left right : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition left) δ →
        HasMeshBelow (TaggedPartition[_,_].partition right) δ →
        riemannSum left f Real.Base.≈ᶜ[ ε /2₊ ] riemannSum right f) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ (tagged : TaggedPartition[ a , b ]) →
        HasMeshBelow (TaggedPartition[_,_].partition tagged) δ →
        riemannSum tagged f Real.Base.≈ᶜ[ ε ] quadratureValue q)
  use-stability-radius (δ , compare) =
    PT.rec squash₁ use-mesh-tail (mesh→0 δ)
    where
    use-mesh-tail :
      Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n →
          HasMeshBelow
            (TaggedPartition[_,_].partition (partitions n)) δ) →
      ∃[ δ' ∈ ℚ₊ ]
        (∀ (tagged : TaggedPartition[ a , b ]) →
          HasMeshBelow (TaggedPartition[_,_].partition tagged) δ' →
          riemannSum tagged f Real.Base.≈ᶜ[ ε ] quadratureValue q)
    use-mesh-tail (N , fine) =
      PT.map
        (λ { (M , close-to-limit) →
          δ , λ tagged tagged-fine →
            let k = max N M
            in subst
              (λ ρ →
                riemannSum tagged f
                  Real.Base.≈ᶜ[ ρ ] quadratureValue q)
              (ℚ₊≡ (/2+/2≡id (fst ε)))
              (Real.Approximation.tri≈ᶜ
                (riemannSum tagged f)
                (quadratureSequence partitions f k)
                (quadratureValue q)
                (ε /2₊) (ε /2₊)
                (compare tagged (partitions k) tagged-fine
                  (fine k (ℕ.left-≤-max {m = N} {n = M})))
                (close-to-limit k
                  (ℕ.right-≤-max {n = M} {m = N}))) })
        (quadratureValueIsLimit q (ε /2₊))


riemannCauchyGivesWitness : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ])
  (mesh→0 : HasVanishingMesh partitions)
  (stable : IsRiemannCauchy f) →
  RiemannIntegralWitness {a} {b} f
riemannCauchyGivesWitness {a} {b} {f = f}
  partitions mesh→0 stable =
  quadratureValue q ,
  riemannCauchyLimitIsRiemannIntegral
    {a = a} {b = b} {f = f} partitions mesh→0 stable
  where
  q = riemannCauchyGivesCauchyQuadrature
    {a = a} {b = b} {f = f} partitions mesh→0 stable


riemannCauchyGivesMereIntegrability : ∀ {a b f}
  (partitions : ℕ → TaggedPartition[ a , b ]) →
  HasVanishingMesh partitions →
  IsRiemannCauchy f →
  MerelyRiemannIntegrable {a} {b} f
riemannCauchyGivesMereIntegrability {a} {b} {f = f}
  partitions mesh→0 stable =
  ∣ riemannCauchyGivesWitness
      {a = a} {b = b} {f = f} partitions mesh→0 stable ∣₁


-- Conversely, two fine sums are close through the integral value.  Thus on
-- intervals carrying a vanishing-mesh family the criterion is not weaker
-- than Riemann integrability; it is the value-free formulation of it.

riemannIntegralGivesRiemannCauchy : ∀ {a b f value} →
  IsRiemannIntegral {a} {b} f value →
  IsRiemannCauchy {a} {b} f
riemannIntegralGivesRiemannCauchy
  {a} {b} {f = f} {value = value} integral ε =
  PT.map
    (λ { (δ , close-to-value) →
      δ , λ left right left-fine right-fine →
        subst
          (λ ρ →
            riemannSum left f Real.Base.≈ᶜ[ ρ ] riemannSum right f)
          (ℚ₊≡ (/2+/2≡id (fst ε)))
          (Real.Approximation.tri≈ᶜ
            (riemannSum left f) value (riemannSum right f)
            (ε /2₊) (ε /2₊)
            (close-to-value left left-fine)
            (Real.Base.sym≈ᶜ
              (riemannSum right f) value (ε /2₊)
              (close-to-value right right-fine))) })
    (integral (ε /2₊))


-- Remaining analytic boundary: radiuswise uniform continuity should imply
-- `IsRiemannCauchy`.  Unlike same-partition resampling, that theorem must
-- compare different vertex sets.  It needs a checked common-refinement or
-- overlap-weight construction; assuming it here would conceal the central
-- geometric argument, so this module deliberately stops at the exact
-- value-free criterion that such a construction must provide.
