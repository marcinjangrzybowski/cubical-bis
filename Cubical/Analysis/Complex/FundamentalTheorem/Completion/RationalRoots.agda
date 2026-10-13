open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.RationalRoots (n : ℕ) where

-- Rational coefficient vectors admit deterministic Gaussian factor
-- approximations. Dyadic accuracies give an explicit coefficient Cauchy
-- witness, and the reflected root witness supplies a completed multiset.

open import Cubical.Foundations.Prelude
import Cubical.Data.Nat.Order as N
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Vec using (Vec; map)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.Rationals.Inverse using (1/2ⁿ<ε)
open import Cubical.Data.Rationals.Order.Algebra using (_ℚ₊^ⁿ_)
import Cubical.Data.Rationals.Order as Q
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open OrderedCommRingTheory ℚOrderedCommRing using (powExponentAntitone)
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.RationalFactors
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n using (module R)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.SequentialClosure n

private
  module CT = PremetricTheory (coefficientSpace n)

  dyadic : ℕ → ℚ₊
  dyadic k = [ 1 / 2 ]₊ ℚ₊^ⁿ k

  index : ℚ₊ → ℕ
  index ε = fst (1/2ⁿ<ε ε)

  half-below-one : fst [ 1 / 2 ]₊ Q.< 1
  half-below-one = subst (fst [ 1 / 2 ]₊ Q.<_) (1/2∈ℚ./2+/2≡id 1)
    (<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  late-small : ∀ ε k → index ε N.≤ k → dyadic k ≤₊ ε
  late-small ε k late = Q.isTrans≤ (fst (dyadic k)) (fst (dyadic (index ε))) (fst ε)
    (powExponentAntitone (fst [ 1 / 2 ]₊)
      (Q.<Weaken≤ 0 (fst [ 1 / 2 ]₊) (snd [ 1 / 2 ]₊))
      (Q.<Weaken≤ (fst [ 1 / 2 ]₊) 1 half-below-one) (index ε) k late)
    (Q.<Weaken≤ (fst (dyadic (index ε))) (fst ε) (snd (1/2ⁿ<ε ε)))

opaque
  rational-rootFiber : ∀ (p : Vec GaussianRational n) → RootFiber (map gaussianℂ p)
  rational-rootFiber p = rootFiber-limit ps PT.∣ witness ∣₁ (map gaussianℂ p) converges
    (λ k → R.insert (qs k) , joint-insert (qs k))
    where
    qs : ℕ → Vec GaussianRational n
    qs k = fst (chosenRationalFactors p (dyadic k))

    ps : ℕ → MonicPolynomial n
    ps k = gaussianFactors (qs k)

    error : ∀ k → CoefficientCloseness (ps k) (dyadic k) (map gaussianℂ p)
    error k = coefficientCloseness-sym (map gaussianℂ p) (ps k) (dyadic k)
      (snd (chosenRationalFactors p (dyadic k)))

    approximate : ∀ ε k → index ε N.≤ k → CoefficientCloseness (ps k) ε (map gaussianℂ p)
    approximate ε k late = coefficientCloseness-monotone (ps k) (map gaussianℂ p) (dyadic k) ε
      (late-small ε k late) (error k)

    witness : CT.isCauchySeq ps
    witness = (λ ε → index (ε /2₊)) , λ ε k l late-k late-l →
      coefficientCloseness-halfTriangle (ps k) (map gaussianℂ p) (ps l) ε
        (approximate (ε /2₊) k late-k)
        (coefficientCloseness-sym (ps l) (map gaussianℂ p) (ε /2₊) (approximate (ε /2₊) l late-l))

    converges : CT.isLimitSeq ps (map gaussianℂ p)
    converges ε = PT.∣ index ε , approximate ε ∣₁
