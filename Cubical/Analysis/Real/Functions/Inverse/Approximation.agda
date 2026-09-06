module Cubical.Analysis.Real.Functions.Inverse.Approximation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base hiding (width)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base using (fineTaggedPartition)


-- Radiuswise uniform continuity: each output radius merely has a suitable
-- input radius. No single function choosing all such radii is required.
IntervalUniformContinuity : (ℝ → ℝ) → ℝ → ℝ → Type₀
IntervalUniformContinuity f a b = ∀ ε →
  ∃[ δ ∈ ℚ₊ ] (∀ (x y : ClosedInterval a b) →
    fst x ∼[ δ ] fst y → f (fst x) ∼[ ε ] f (fst y))

-- A radiuswise estimate, with no globally selected reflection modulus.
IntervalClosenessReflection : (ℝ → ℝ) → ℝ → ℝ → Type₀
IntervalClosenessReflection f a b = ∀ ε →
  ∃[ δ ∈ ℚ₊ ] (∀ (x y : ClosedInterval a b) →
    f (fst x) ∼[ δ ] f (fst y) → fst x ∼[ ε ] fst y)

ApproximateIntervalPreimage : (ℝ → ℝ) → ℝ → ℝ → ℝ → ℚ₊ → Type₀
ApproximateIntervalPreimage f a b target ε =
  Σ[ point ∈ ClosedInterval a b ] f (fst point) ∼[ ε ] target


private
  selfDifferenceSmall : ∀ x ε → absℝ (x - x) <ℝ rat (fst ε)
  selfDifferenceSmall x ε =
    subst (_<ℝ rat (fst ε)) (sym (cong absℝ (subSelf x) ∙ absZero))
      (positiveSlack ε)

  -- A finite chain must cross the overlapping target band. Its index stays
  -- truncated: neither decidable real comparisons nor countable choice occur.
  finiteChainApproximation : ∀ {n} (values : FinVec ℝ (suc n)) target slack →
    (∀ i → values (FD.suc i) ∼[ slack ] values (FD.weakenFin i)) →
    values FD.zero <ℝ target + rat (fst slack) →
    target - rat (fst slack) <ℝ values (FD.fromℕ n) →
    ∥ Σ[ i ∈ Fin (suc n) ] values i ∼[ slack +₊ slack ] target ∥₁
  finiteChainApproximation {zero} values target slack close below above =
    ∣ FD.zero , slackBracketImagesClose
      (values FD.zero) (values FD.zero) target slack below above
      (selfDifferenceSmall (values FD.zero) slack) ∣₁
  finiteChainApproximation {suc n} values target slack close below above =
    PT.rec squash₁ (⊎.rec continue finish)
      (dichotomyℝ (target - rat (fst slack))
        (values (FD.suc FD.zero)) (target + rat (fst slack))
        (slackBand target slack))
    where
    continue : values (FD.suc FD.zero) <ℝ target + rat (fst slack) →
      ∥ Σ[ i ∈ Fin (suc (suc n)) ] values i ∼[ slack +₊ slack ] target ∥₁
    continue next-below =
      PT.map (λ { (i , near) → FD.suc i , near })
        (finiteChainApproximation (values ∘ FD.suc) target slack
          (λ i → close (FD.suc i)) next-below above)

    finish : target - rat (fst slack) <ℝ values (FD.suc FD.zero) →
      ∥ Σ[ i ∈ Fin (suc (suc n)) ] values i ∼[ slack +₊ slack ] target ∥₁
    finish next-above =
      ∣ FD.zero , slackBracketImagesClose
        (values FD.zero) (values (FD.suc FD.zero)) target slack below next-above
        (closeness→absDifference<
          (values (FD.suc FD.zero)) (values FD.zero) slack (close FD.zero)) ∣₁


opaque
  intervalApproximateIntermediateValue : ∀ f a b → a ≤ℝ b →
    IntervalUniformContinuity f a b → ∀ target →
    f a ≤ℝ target → target ≤ℝ f b → ∀ tolerance →
    ∥ ApproximateIntervalPreimage f a b target tolerance ∥₁
  intervalApproximateIntermediateValue f a b ordered continuous
      target lower upper tolerance =
    PT.rec squash₁
      (λ { (δ , preserves) →
        PT.rec squash₁ (fromPartition δ preserves)
          (fineTaggedPartition a b ordered δ) })
      (continuous slack)
    where
    slack : ℚ₊
    slack = tolerance /2₊

    fromPartition : ∀ δ →
      (∀ (x y : ClosedInterval a b) →
        fst x ∼[ δ ] fst y → f (fst x) ∼[ slack ] f (fst y)) →
      (Σ[ tagged ∈ TaggedPartition[ a , b ] ]
        HasMeshBelow (TaggedPartition.partition tagged) δ) →
      ∥ ApproximateIntervalPreimage f a b target tolerance ∥₁
    fromPartition δ preserves (tagged , mesh) =
      PT.map
        (λ { (i , near) → point i ,
          subst (λ ε → f (points i) ∼[ ε ] target)
            (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst tolerance))) near })
        (finiteChainApproximation (f ∘ points) target slack adjacent below above)
      where
      partition : Partition[ a , b ]
      partition = TaggedPartition.partition tagged

      points : FinVec ℝ (suc (Partition.intervalCount partition))
      points = Partition.points partition

      point : Fin (suc (Partition.intervalCount partition)) → ClosedInterval a b
      point i = points i , partitionPointLowerBound partition i
        , partitionPointUpperBound partition i

      adjacent : ∀ i → f (points (FD.suc i)) ∼[ slack ]
        f (points (FD.weakenFin i))
      adjacent i = preserves (point (FD.suc i)) (point (FD.weakenFin i))
        (absDifference<→closeness
          (points (FD.suc i)) (points (FD.weakenFin i)) δ
          (subst (_<ℝ rat (fst δ))
            (sym (absOfNonnegative (width partition i) (width-nonnegative partition i)))
            (mesh i)))

      below : f (points FD.zero) <ℝ target + rat (fst slack)
      below = subst (_<ℝ target + rat (fst slack))
        (sym (cong f (Partition.leftEndpoint partition)))
        (≤<ℝ-trans (f a) target (target + rat (fst slack))
          lower (rightSlack target slack))

      above : target - rat (fst slack) <ℝ
        f (points (FD.fromℕ (Partition.intervalCount partition)))
      above = subst (target - rat (fst slack) <ℝ_)
        (sym (cong f (Partition.rightEndpoint partition)))
        (<≤ℝ-trans (target - rat (fst slack)) target (f b)
          (leftSlack target slack) upper)
