open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Extension (n : ℕ) where

-- Extend the finite factor map by the native sequential eliminator.
-- Induction supplies a sequence of UNIQUE graph values. The image Cauchy
-- witness is computed from the source witness and one whole local
-- modulus, rather than selected from radiuswise approximation witnesses.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; _/4₊)
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Base
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n

private
  module B = Roots n
  module S = B.S
  module P = B.P
  module CT = PremetricTheory (coefficientSpace n)

opaque
  graph-image-cauchy : ∀ (xs : ℕ → R.Carrier) (gx : S.SeqWitness xs) (ps : ℕ → MonicPolynomial n) →
    (∀ k → Joint (xs k) (ps k)) → PT.∥ CT.isCauchySeq ps ∥₁
  graph-image-cauchy xs gx ps joint = PT.rec PT.isPropPropTrunc withModulus (factor-centered (S.lim xs gx))
    where
    withModulus : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorCenteredAt (S.lim xs gx) μ) → PT.∥ CT.isCauchySeq ps ∥₁
    withModulus (μ , centered) = PT.map makeWitness gx
      where
      small radius : ℚ₊ → ℚ₊
      small ε = (ε /2₊) /2₊
      radius ε = μ (small ε) /2₊

      makeWitness : S.CauchySeq xs → CT.isCauchySeq ps
      makeWitness (K , tail) = (λ ε → K ((radius ε /4₊) /4₊)) , λ ε k l late-k late-l →
        PT.rec2 (coefficientCloseness-prop (ps k) (ps l) ε)
          (λ { (qs , near-q , factor-q) (rs , near-r , factor-r) →
            coefficientCloseness-threeParts (ps k) (gaussianFactors qs) (gaussianFactors rs) (ps l) ε
              (coefficientCloseness-sym (gaussianFactors qs) (ps k) (small ε) factor-q)
              (centered (small ε) qs rs
                (R.subst≈ (R.insert qs) (S.lim xs gx) (1/2∈ℚ./2+/2≡id (fst (μ (small ε))))
                  (R.isTriangular≈ (R.insert qs) (xs k) (S.lim xs gx) (radius ε) (radius ε) near-q
                    (P.close-lim-from-late (xs k) xs gx K tail (radius ε) k late-k
                      (R.isRefl≈ (xs k) (((radius ε /4₊) /4₊) /4₊)))))
                (R.subst≈ (R.insert rs) (S.lim xs gx) (1/2∈ℚ./2+/2≡id (fst (μ (small ε))))
                  (R.isTriangular≈ (R.insert rs) (xs l) (S.lim xs gx) (radius ε) (radius ε) near-r
                    (P.close-lim-from-late (xs l) xs gx K tail (radius ε) l late-l
                      (R.isRefl≈ (xs l) (((radius ε /4₊) /4₊) /4₊)))))) factor-r })
          (joint k (radius ε) (small ε)) (joint l (radius ε) (small ε))

private
  baseFiber : ∀ q → FactorFiber (S.ι q)
  baseFiber = SQ.elimProp (λ q → isPropFactorFiber (S.ι q))
    (λ qs → gaussianFactors qs , joint-insert qs)

  limitFiber : ∀ xs gx → (∀ k → FactorFiber (xs k)) → FactorFiber (S.lim xs gx)
  limitFiber xs gx fibers = fst output , joint-limit xs ps (S.lim xs gx) (fst output)
    (λ k → snd (fibers k)) (P.lim-isLimitSeq xs gx) (snd output)
    where
    ps : ℕ → MonicPolynomial n
    ps k = fst (fibers k)

    output : CT.limitSeq ps
    output = coefficients-sequentiallyComplete n ps
      (graph-image-cauchy xs gx ps (λ k → snd (fibers k)))

  factorElim : S.Elimℭ̂ₛ-Prop FactorFiber
  factorElim .S.Elimℭ̂ₛ-Prop.ιA = baseFiber
  factorElim .S.Elimℭ̂ₛ-Prop.limA = limitFiber
  factorElim .S.Elimℭ̂ₛ-Prop.isPropA = isPropFactorFiber

opaque
  factorFiber : ∀ x → FactorFiber x
  factorFiber = S.Elimℭ̂ₛ-Prop.go factorElim

completedFactors : R.Carrier → MonicPolynomial n
completedFactors x = fst (factorFiber x)

completedFactors-joint : ∀ x → Joint x (completedFactors x)
completedFactors-joint x = snd (factorFiber x)

completedFactors-insert : ∀ qs → completedFactors (R.insert qs) ≡ gaussianFactors qs
completedFactors-insert qs = joint-coefficients-unique (R.insert qs)
  (completedFactors (R.insert qs)) (gaussianFactors qs) (completedFactors-joint (R.insert qs)) (joint-insert qs)
