open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.SequentialClosure (n : ℕ) where

-- The image is closed under native Cauchy limits. The supplied witness
-- contains one whole modulus; radiuswise convergence alone is not used to
-- manufacture one. Root matching gives the reflected Cauchy modulus.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (max)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n using (module R)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.GraphContinuity n

private
  module RT = PremetricTheory R.space
  module CT = PremetricTheory (coefficientSpace n)

RootFiber : MonicPolynomial n → Type₀
RootFiber p = Σ[ x ∈ R.Carrier ] Joint x p

isPropRootFiber : ∀ p → isProp (RootFiber p)
isPropRootFiber p (x , xp) (y , yp) = Σ≡Prop (λ z → isPropJoint z p) (joint-roots-unique x y p xp yp)

opaque
  graph-reflects-cauchy : ∀ (ps : ℕ → MonicPolynomial n) (xs : ℕ → R.Carrier) →
    (∀ k → Joint (xs k) (ps k)) → PT.∥ CT.isCauchySeq ps ∥₁ → PT.∥ RT.isCauchySeq xs ∥₁
  graph-reflects-cauchy ps xs joint = PT.rec PT.isPropPropTrunc withWitness
    where
    withWitness : CT.isCauchySeq ps → PT.∥ RT.isCauchySeq xs ∥₁
    withWitness (K , tail) = PT.map withBound (coefficientBound-exists (ps (K 1)))
      where
      withBound : (Σ[ A ∈ ℚ₊ ] CoefficientsBounded (ps (K 1)) A) → RT.isCauchySeq xs
      withBound (A , bounded) = (λ ε → max (K 1) (K (rootGraphRadius (A +₊ (1 +₊ 1)) ε))) ,
        λ ε k l late-k late-l → joint-root-estimate (ps k) (A +₊ (1 +₊ 1))
          (nearbyCoefficient-bound (ps (K 1)) (ps k) A bounded
            (tail 1 (K 1) k N.≤-refl (N.≤-trans (N.left-≤-max {m = K 1} {n = K (rootGraphRadius (A +₊ (1 +₊ 1)) ε)}) late-k)))
          ε (xs k) (xs l) (ps l) (joint k) (joint l)
          (tail (rootGraphRadius (A +₊ (1 +₊ 1)) ε) k l
            (N.≤-trans (N.right-≤-max {n = K (rootGraphRadius (A +₊ (1 +₊ 1)) ε)} {m = K 1}) late-k) (N.≤-trans (N.right-≤-max {n = K (rootGraphRadius (A +₊ (1 +₊ 1)) ε)} {m = K 1}) late-l))

  rootFiber-limit : ∀ (ps : ℕ → MonicPolynomial n) → PT.∥ CT.isCauchySeq ps ∥₁ →
    ∀ p → CT.isLimitSeq ps p → (∀ k → RootFiber (ps k)) → RootFiber p
  rootFiber-limit ps witness p converges fibers = fst output ,
    joint-limit xs ps (fst output) p (λ k → snd (fibers k)) (snd output) converges
    where
    xs : ℕ → R.Carrier
    xs k = fst (fibers k)

    output : RT.limitSeq xs
    output = R.sequentiallyComplete xs (graph-reflects-cauchy ps xs (λ k → snd (fibers k)) witness)
