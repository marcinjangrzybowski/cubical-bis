module Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumChain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteIndices
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumStep

module FiniteNearMaxima {n} (coefficients : Fin (suc n) → ℝ) (q : ℝ) (ε : ℚ₊) where
  -- A dependent finite chain records the global comparison invariant at
  -- every radius. There is no quantification over a chosen infinite path.
  NearMaximumChain : ℕ → ℝ → Fin (suc n) → Type₀
  NearMaximumChain zero r k = PowerNearMaximum coefficients r ε k
  NearMaximumChain (suc steps) r k = PowerNearMaximum coefficients r ε k ×
    (Σ[ j ∈ Fin (suc n) ] (Fin.toℕ j ℕ.≤ Fin.toℕ k) × NearMaximumChain steps (q · r) j)

  buildNearMaximumChain :
    (∀ i → 0ℝ ≤ℝ coefficients i) → 0ℝ <ℝ q → q ≤ℝ 1ℝ →
    q · rat (fst ε) ≤ℝ rat (fst (ε /2₊)) →
    (steps : ℕ) (r : ℝ) → 0ℝ <ℝ r → (k : Fin (suc n)) →
    PowerNearMaximum coefficients r ε k → ∥ NearMaximumChain steps r k ∥₁
  buildNearMaximumChain nonnegative q-positive q-small error zero r r-positive k maximum = ∣ maximum ∣₁
  buildNearMaximumChain nonnegative q-positive q-small error (suc steps) r r-positive k maximum =
    PT.rec squash₁
      (λ (j , decreases , next-maximum) → PT.map (λ tail → maximum , j , decreases , tail)
        (buildNearMaximumChain nonnegative q-positive q-small error steps (q · r)
          (mulPositive q r q-positive r-positive) j next-maximum))
      (nextPowerNearMaximum coefficients q r ε k nonnegative q-positive q-small
        (<ℝ-weaken 0ℝ r r-positive) error maximum)

  chainTail : ∀ steps r k → NearMaximumChain steps r k → Vec ℕ steps
  chainTail zero r k maximum = []
  chainTail (suc steps) r k (maximum , j , decreases , tail) =
    Fin.toℕ j ∷ chainTail steps (q · r) j tail

  chainIndices : ∀ steps r k → NearMaximumChain steps r k → Vec ℕ (suc steps)
  chainIndices steps r k chain = Fin.toℕ k ∷ chainTail steps r k chain

  chainNonIncreasing : ∀ steps r k (chain : NearMaximumChain steps r k) →
    NonIncreasingIndices (chainIndices steps r k chain)
  chainNonIncreasing zero r k maximum = tt
  chainNonIncreasing (suc steps) r k (maximum , j , decreases , tail) =
    decreases , chainNonIncreasing steps (q · r) j tail

  tripleSteps : ℕ
  tripleSteps = suc (suc (twiceIndexBound n))

  finiteNearMaximumTriple :
    (∀ i → 0ℝ ≤ℝ coefficients i) → 0ℝ <ℝ q → q ≤ℝ 1ℝ →
    q · rat (fst ε) ≤ℝ rat (fst (ε /2₊)) →
    (r : ℝ) → 0ℝ <ℝ r → (k : Fin (suc n)) → PowerNearMaximum coefficients r ε k →
    ∥ Σ[ chain ∈ NearMaximumChain tripleSteps r k ]
      EqualIndexTriple (chainIndices tripleSteps r k chain) ∥₁
  finiteNearMaximumTriple nonnegative q-positive q-small error r r-positive k maximum = PT.map
    (λ chain → chain , finiteEqualIndexTriple n (chainIndices tripleSteps r k chain)
      (ℕ.pred-≤-pred (Fin.toℕ<n k)) (chainNonIncreasing tripleSteps r k chain))
    (buildNearMaximumChain nonnegative q-positive q-small error tripleSteps r r-positive k maximum)
