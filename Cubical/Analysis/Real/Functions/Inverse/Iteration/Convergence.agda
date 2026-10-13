module Cubical.Analysis.Real.Functions.Inverse.Iteration.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Functions.Inverse.Iteration.Base
open import Cubical.Analysis.Real.Functions.Inverse.Iteration.Rate

module Convergence
  (f : ℝ → ℝ) (a b target : ℝ)
  (ordered : a ≤ℝ b)
  (lower-image : f a ≤ℝ target) (upper-image : target ≤ℝ f b)
  (monotone : ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → f x ≤ℝ f y)
  (upper-difference : ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b →
    f y - f x ≤ℝ y - x) where

  open Iteration f a b target ordered lower-image upper-image monotone upper-difference

  module WithBound (bound : ℚ₊) (width-bound : b - a ≤ℝ rat (fst bound)) where
    private
      residualRate : ∀ (tolerance : ℚ₊) →
        Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → residual (points n) <ℝ rat (fst tolerance))
      residualRate = weightedBoundHasExplicitRate (λ n → residual (points n)) bound
        (λ n → residual-nonnegative (points n) (points-invariant n))
        (λ n → ≤ℝ-trans (realNatural n · residual (points n)) (b - a) (rat (fst bound))
          (weighted-residual-bound n) width-bound)

    opaque
      imageRate : ∀ tolerance →
        Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → f (points n) ∼[ tolerance ] target)
      imageRate tolerance = fst (residualRate tolerance) , λ n late →
        absDifference<→closeness (f (points n)) target tolerance
          (subst (_<ℝ rat (fst tolerance))
            (sym (absSubComm (f (points n)) target
              ∙ absOfNonnegative (residual (points n))
                (residual-nonnegative (points n) (points-invariant n))))
            (snd (residualRate tolerance) n late))

      imageCauchy : CauchySeq (λ n → f (points n))
      imageCauchy = (λ ε → fst (imageRate (ε /2₊))) , λ ε m n late-m late-n →
        subst (λ δ → f (points m) ∼[ δ ] f (points n))
          (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst ε)))
          (triangle∼ (f (points m)) target (f (points n)) (ε /2₊) (ε /2₊)
            (snd (imageRate (ε /2₊)) m late-m)
            (sym∼ (f (points n)) target (ε /2₊) (snd (imageRate (ε /2₊)) n late-n)))

      imageLimit : isLimitSequence (λ n → f (points n)) target
      imageLimit ε = ∣ imageRate ε ∣₁

  -- A single bound on the bracket width is unpacked into a proposition.
  -- Within it the rational formula supplies the entire Cauchy modulus.
  opaque
    imagesConverge : SeqWitness (λ n → f (points n)) ×
      isLimitSequence (λ n → f (points n)) target
    imagesConverge = PT.rec (isProp× squash₁ (isPropIsLimitSequence _ target))
      (λ { (n , large) →
        let bounded = <ℝ-weaken (b - a) (rat (naturalRational n)) large
        in ∣ WithBound.imageCauchy (naturalBound n) bounded ∣₁
          , WithBound.imageLimit (naturalBound n) bounded })
      (∃naturalUpperBound (b - a))

  -- Perform the interval projection conversion while f is still a variable.
  opaque
    intervalImagesConverge : SeqWitness (λ n → f (fst (intervalPoints n))) ×
      isLimitSequence (λ n → f (fst (intervalPoints n))) target
    intervalImagesConverge = imagesConverge

  opaque
    convergentIntervalImages :
      Σ[ samples ∈ (ℕ → ClosedInterval a b) ]
        SeqWitness (λ n → f (fst (samples n))) ×
        isLimitSequence (λ n → f (fst (samples n))) target
    convergentIntervalImages = intervalPoints , intervalImagesConverge
