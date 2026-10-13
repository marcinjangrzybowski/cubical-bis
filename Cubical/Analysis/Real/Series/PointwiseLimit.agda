module Cubical.Analysis.Real.Series.PointwiseLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform

open PositiveRationals using (ℚ₊; _+₊_; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; _/4₊; /2₊<id)
open 1/2∈ℚ using (/2+/2≡id; /4+/4≡/2)

-- Finite summation commutes with pointwise sequence limits. This is the
-- prefix-sum form of finite-sum continuity, proved by its additive recursion.
partialSumPresPointwiseLimit : ∀ (terms : ℕ → RealSequence) values →
  (∀ k → isLimitSequence (λ index → terms index k) (values k)) → ∀ count →
  isLimitSequence (λ index → partialSum (terms index) count) (partialSum values count)
partialSumPresPointwiseLimit terms values pointwise zero = constantIsLimitSequence 0ℝ
partialSumPresPointwiseLimit terms values pointwise (suc count) =
  addPresIsLimitSequence (partialSumPresPointwiseLimit terms values pointwise count) (pointwise count)

-- A common native modulus survives pointwise limits, with one fixed loss
-- of precision. The pointwise limits are never used to choose a modulus.
opaque
  uniformlyCauchyPointwiseLimitIsCauchy : ∀ (terms : ℕ → RealSequence) values →
    UniformlyCauchySeries ℕ terms →
    (∀ k → isLimitSequence (λ index → terms index k) (values k)) →
    IsCauchySeries values
  uniformlyCauchyPointwiseLimitIsCauchy terms values uniform pointwise = PT.map chosen uniform
    where
    chosen : ChosenUniformlyCauchySeries ℕ terms → ChosenIsCauchySequence (partialSum values)
    chosen (modulus , close) = (λ ε → modulus (ε /2₊)) , tail
      where
      tail : ∀ ε m n → modulus (ε /2₊) Nat.≤ m → modulus (ε /2₊) Nat.≤ n →
        partialSum values m ∼[ ε ] partialSum values n
      tail ε m n lateM lateN = absDifference<→closeness (partialSum values m) (partialSum values n) ε
        (≤<ℝ-trans (absℝ (partialSum values m - partialSum values n))
          (rat (fst (ε /2₊))) (rat (fst ε)) closedBound
          (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
        where
        closedBound : absℝ (partialSum values m - partialSum values n) ≤ℝ rat (fst (ε /2₊))
        closedBound = pointwiseLePresLimits
          (λ index → <ℝ-weaken (absℝ (partialSum (terms index) m - partialSum (terms index) n))
            (rat (fst (ε /2₊)))
            (closeness→absDifference< (partialSum (terms index) m) (partialSum (terms index) n)
              (ε /2₊) (close index (ε /2₊) m n lateM lateN)))
          (continuousPreservesIsLimitSequence absℝ abs-isContinuous (subPresIsLimitSequence
            (partialSumPresPointwiseLimit terms values pointwise m)
            (partialSumPresPointwiseLimit terms values pointwise n)))
          (constantIsLimitSequence (rat (fst (ε /2₊))))

-- Uniform summation permits exchanging an ordinary pointwise sequence
-- limit with the series sum. All three sums/limits are explicit inputs.
opaque
  uniformSeriesSumsPresPointwiseLimit : ∀ (terms : ℕ → RealSequence) values sums value →
    UniformHasSum terms sums →
    (∀ k → isLimitSequence (λ index → terms index k) (values k)) →
    HasSum values value → isLimitSequence sums value
  uniformSeriesSumsPresPointwiseLimit terms values sums value uniform pointwise summed ε =
    PT.rec squash₁ withUniform (uniform (ε /2₊))
    where
    withUniform :
      (Σ[ cutoff ∈ ℕ ] (∀ index n → cutoff Nat.≤ n → partialSum (terms index) n ∼[ ε /2₊ ] sums index)) →
      ∥ Σ[ cutoff ∈ ℕ ] (∀ index → cutoff Nat.≤ index → sums index ∼[ ε ] value) ∥₁
    withUniform (first , closeFirst) = PT.rec squash₁ withSum (summed (ε /4₊))
      where
      withSum : (Σ[ cutoff ∈ ℕ ] (∀ n → cutoff Nat.≤ n → partialSum values n ∼[ ε /4₊ ] value)) →
        ∥ Σ[ cutoff ∈ ℕ ] (∀ index → cutoff Nat.≤ index → sums index ∼[ ε ] value) ∥₁
      withSum (second , closeSecond) = PT.map finish
        (partialSumPresPointwiseLimit terms values pointwise count (ε /4₊))
        where
        count : ℕ
        count = Nat.max first second

        finish : (Σ[ cutoff ∈ ℕ ] (∀ index → cutoff Nat.≤ index →
            partialSum (terms index) count ∼[ ε /4₊ ] partialSum values count)) →
          Σ[ cutoff ∈ ℕ ] (∀ index → cutoff Nat.≤ index → sums index ∼[ ε ] value)
        finish (cutoff , closeHead) = cutoff , λ index late →
          subst (sums index ∼[_] value) (ℚ₊≡ (/2+/2≡id (fst ε)))
            (triangle∼ (sums index) (partialSum (terms index) count) value (ε /2₊) (ε /2₊)
              (sym∼ (partialSum (terms index) count) (sums index) (ε /2₊)
                (closeFirst index count (Nat.left-≤-max {m = first} {n = second})))
              (subst (partialSum (terms index) count ∼[_] value) (ℚ₊≡ (/4+/4≡/2 (fst ε)))
                (triangle∼ (partialSum (terms index) count) (partialSum values count) value (ε /4₊) (ε /4₊)
                  (closeHead index late) (closeSecond count (Nat.right-≤-max {n = second} {m = first})))))
