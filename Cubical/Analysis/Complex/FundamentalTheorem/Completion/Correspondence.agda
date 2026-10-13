open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Correspondence (n : ℕ) where

-- Rational search supplies the base case; native coefficient induction
-- and reflected Cauchy limits supply the general case. The result is an
-- unordered completed multiset, not a chosen tuple of native roots.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Base
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.CoefficientInduction
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n using (module R)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.GraphContinuity n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Extension n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FactorMap n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.SequentialClosure n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.RationalRoots n

opaque
  rootFiber : ∀ p → RootFiber p
  rootFiber = coefficientInduction n RootFiber isPropRootFiber rational-rootFiber rootFiber-limit

completedRoots : MonicPolynomial n → R.Carrier
completedRoots p = fst (rootFiber p)

completedRoots-joint : ∀ p → Joint (completedRoots p) p
completedRoots-joint p = snd (rootFiber p)

opaque
  factors-roots : ∀ p → completedFactors (completedRoots p) ≡ p
  factors-roots p = joint-coefficients-unique (completedRoots p) (completedFactors (completedRoots p)) p
    (completedFactors-joint (completedRoots p)) (completedRoots-joint p)

  roots-factors : ∀ x → completedRoots (completedFactors x) ≡ x
  roots-factors x = joint-roots-unique (completedRoots (completedFactors x)) x (completedFactors x)
    (completedRoots-joint (completedFactors x)) (completedFactors-joint x)

completedFactorIso : Iso R.Carrier (MonicPolynomial n)
completedFactorIso .Iso.fun = completedFactors
completedFactorIso .Iso.inv = completedRoots
completedFactorIso .Iso.sec = factors-roots
completedFactorIso .Iso.ret = roots-factors

completedFactorEquivalence : R.Carrier ≃ MonicPolynomial n
completedFactorEquivalence = isoToEquiv completedFactorIso

rootMultisetCorrespondence : RootMultisetCorrespondence (rootMultisetCompletion n)
CompletionCorrespondence.factorEquivalence rootMultisetCorrespondence = completedFactorEquivalence
CompletionCorrespondence.agreesOnFiniteFactors rootMultisetCorrespondence = completedFactors-insert
CompletionCorrespondence.factorContinuity rootMultisetCorrespondence = completedFactors-continuity
CompletionCorrespondence.rootContinuity rootMultisetCorrespondence p = PT.map
  (λ { (μ , preserve) → μ , λ ε q close → preserve ε (completedRoots p) (completedRoots q) q
    (completedRoots-joint p) (completedRoots-joint q) close }) (joint-root-continuity p)
