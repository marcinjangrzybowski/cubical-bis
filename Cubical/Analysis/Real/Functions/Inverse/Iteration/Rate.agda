module Cubical.Analysis.Real.Functions.Inverse.Iteration.Rate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (fromNat)
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order.Floor using (ceilℚ₊)
open import Cubical.Data.Rationals.Inverse using (_₊／₊_; ·／)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties

private
  module O = OrderedCommRingTheory ℝOrderedCommRing

-- A rational ceiling gives one explicit cutoff for each tolerance.
-- The only real-valued input is the separately supplied bound on n*u(n).
weightedCutoff : ℚ₊ → ℚ₊ → ℕ
weightedCutoff bound tolerance = ℕ₊₁→ℕ (fst (ceilℚ₊ (bound ₊／₊ tolerance)))

opaque
  weightedCutoff-positive : ∀ bound tolerance →
    0ℝ <ℝ realNatural (weightedCutoff bound tolerance)
  weightedCutoff-positive bound tolerance =
    <ℚ→<ℝ 0 (fromNat (weightedCutoff bound tolerance))
      (naturalPositive (fst (ceilℚ₊ (bound ₊／₊ tolerance))))

  weightedCutoff-large : ∀ bound tolerance →
    rat (fst bound) <ℝ realNatural (weightedCutoff bound tolerance) · rat (fst tolerance)
  weightedCutoff-large bound tolerance =
    subst (rat (fst bound) <ℝ_)
      (sym (mul-rat (fromNat (weightedCutoff bound tolerance)) (fst tolerance)))
      (<ℚ→<ℝ (fst bound) (fromNat (weightedCutoff bound tolerance) ℚ.· fst tolerance)
        (subst (ℚ._< fromNat (weightedCutoff bound tolerance) ℚ.· fst tolerance)
          (ℚ.·Comm (fst (bound ₊／₊ tolerance)) (fst tolerance) ∙ ·／ tolerance bound)
          (OrderedCommRingStr.·MonoR< (snd ℚOrderedCommRing)
            (fst (bound ₊／₊ tolerance)) (fromNat (weightedCutoff bound tolerance))
            (fst tolerance) (snd tolerance) (snd (ceilℚ₊ (bound ₊／₊ tolerance))))))

  weightedBoundHasExplicitRate : ∀ (u : ℕ → ℝ) (bound : ℚ₊) →
    (∀ n → 0ℝ ≤ℝ u n) →
    (∀ n → realNatural n · u n ≤ℝ rat (fst bound)) →
    ∀ (tolerance : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → u n <ℝ rat (fst tolerance))
  weightedBoundHasExplicitRate u bound nonnegative bounded tolerance =
    N , λ n N≤n → ≤<ℝ-trans (u n) (rat (fst half)) (rat (fst tolerance))
      (O.·CancelL≤ (u n) (rat (fst half)) (realNatural N)
        (weightedCutoff-positive bound half)
        (≤ℝ-trans (realNatural N · u n) (realNatural n · u n)
          (realNatural N · rat (fst half))
          (mulPres≤R-0≤ (realNatural N) (realNatural n) (u n)
            (nonnegative n) (realNatural-mono N≤n))
          (≤ℝ-trans (realNatural n · u n) (rat (fst bound))
            (realNatural N · rat (fst half)) (bounded n)
            (<ℝ-weaken (rat (fst bound)) (realNatural N · rat (fst half))
              (weightedCutoff-large bound half)))))
      (<ℚ→<ℝ (fst half) (fst tolerance) (/2₊<id tolerance))
    where
    half : ℚ₊
    half = tolerance /2₊
    N : ℕ
    N = weightedCutoff bound half
