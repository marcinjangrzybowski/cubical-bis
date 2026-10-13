module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients where

-- The finite coefficient space is complete using native coordinate
-- limits. A finite maximum combines convergence tails; no countable
-- family of chosen coordinate witnesses is needed.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (isoInvInjective)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; FinVec→Vec; FinVec→Vec→FinVec; FinVecIsoVec; module VecPath)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
import Cubical.Data.Rationals.Order as Q
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteMatching as Finite

private
  module C = PremetricStr (snd ℂPremetricSpace)
  module CT = PremetricTheory ℂPremetricSpace
  module F = Finite ℂPremetricSpace

coefficientCloseness-prop : ∀ {n} (p q : MonicPolynomial n) ε → isProp (CoefficientCloseness p ε q)
coefficientCloseness-prop p q ε = isPropΠ λ i → C.isProp≈ (lookup i p) (lookup i q) ε

coefficientCloseness-refl : ∀ {n} (p : MonicPolynomial n) ε → CoefficientCloseness p ε p
coefficientCloseness-refl p ε i = C.isRefl≈ (lookup i p) ε

coefficientCloseness-sym : ∀ {n} (p q : MonicPolynomial n) ε →
  CoefficientCloseness p ε q → CoefficientCloseness q ε p
coefficientCloseness-sym p q ε close i = C.isSym≈ (lookup i p) (lookup i q) ε (close i)

coefficientCloseness-threeParts : ∀ {n} (p q r s : MonicPolynomial n) ε →
  CoefficientCloseness p ((ε /2₊) /2₊) q →
  CoefficientCloseness q ((ε /2₊) /2₊) r →
  CoefficientCloseness r ((ε /2₊) /2₊) s → CoefficientCloseness p ε s
coefficientCloseness-threeParts p q r s ε pq qr rs = coefficientCloseness-halfTriangle p r s ε
  (coefficientCloseness-halfTriangle p q r (ε /2₊) pq qr)
  (coefficientCloseness-monotone r s ((ε /2₊) /2₊) (ε /2₊)
    (Q.<Weaken≤ (fst ((ε /2₊) /2₊)) (fst (ε /2₊)) (/2₊<id (ε /2₊))) rs)

coefficient-ext : ∀ {n} (p q : MonicPolynomial n) → (∀ i → lookup i p ≡ lookup i q) → p ≡ q
coefficient-ext {n} p q equal = isoInvInjective (FinVecIsoVec n) p q (funExt equal)

coefficientCloseness-separated : ∀ {n} (p q : MonicPolynomial n) →
  (∀ ε → CoefficientCloseness p ε q) → p ≡ q
coefficientCloseness-separated p q close = coefficient-ext p q
  (λ i → C.isSeparated≈ (lookup i p) (lookup i q) (λ ε → close ε i))

coefficientSpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
fst (coefficientSpace n) = MonicPolynomial n
PremetricStr._≈[_]_ (snd (coefficientSpace n)) = CoefficientCloseness
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isSetM = VecPath.isOfHLevelVec 0 n isSetℂ
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isProp≈ = coefficientCloseness-prop
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isRefl≈ = coefficientCloseness-refl
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isSym≈ = coefficientCloseness-sym
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isSeparated≈ = coefficientCloseness-separated
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isTriangular≈ p q r ε δ pq qr i =
  C.isTriangular≈ (lookup i p) (lookup i q) (lookup i r) ε δ (pq i) (qr i)
PremetricStr.isPremetric (snd (coefficientSpace n)) .IsPremetric.isRounded≈ p q ε close =
  F.finite-rounded n (λ i → lookup i p) (λ i → lookup i q) ε close

finite-tail : ∀ n (P : Fin n → ℕ → Type₀) →
  (∀ i → PT.∥ Σ[ K ∈ ℕ ] (∀ k → K N.≤ k → P i k) ∥₁) →
  PT.∥ Σ[ K ∈ ℕ ] (∀ k → K N.≤ k → ∀ i → P i k) ∥₁
finite-tail zero P tails = PT.∣ zero , (λ k late ()) ∣₁
finite-tail (suc n) P tails = PT.map2
  (λ { (K , head) (L , tail) → max K L , λ k late → λ
    { zero → head k (N.≤-trans (N.left-≤-max {m = K} {n = L}) late)
    ; (suc i) → tail k (N.≤-trans (N.right-≤-max {n = L} {m = K}) late) i } })
  (tails zero) (finite-tail n (λ i k → P (suc i) k) (λ i → tails (suc i)))

opaque
  complex-sequentiallyComplete : ∀ z → PT.∥ CT.isCauchySeq z ∥₁ → CT.limitSeq z
  complex-sequentiallyComplete z witness = limitℂ z coordinates ,
    complexLimit→premetricLimit z (limitℂ z coordinates) (limitℂ-isLimit z coordinates)
    where
    coordinates : ComplexSeqWitness z
    coordinates = PT.rec (isPropComplexSeqWitness z) (chosenComplexCauchy→witness z) witness

  coefficients-sequentiallyComplete : ∀ n (p : ℕ → MonicPolynomial n) →
    PT.∥ PremetricTheory.isCauchySeq (coefficientSpace n) p ∥₁ →
    PremetricTheory.limitSeq (coefficientSpace n) p
  coefficients-sequentiallyComplete n p witness = result , converges
    where
    coordinateLimit : ∀ i → CT.limitSeq (λ k → lookup i (p k))
    coordinateLimit i = complex-sequentiallyComplete (λ k → lookup i (p k))
      (PT.map (λ { (K , tail) → K , λ ε k l late-k late-l → tail ε k l late-k late-l i }) witness)

    result : MonicPolynomial n
    result = FinVec→Vec (λ i → fst (coordinateLimit i))

    lookup-result : ∀ i → lookup i result ≡ fst (coordinateLimit i)
    lookup-result i = funExt⁻ (FinVec→Vec→FinVec (λ j → fst (coordinateLimit j))) i

    converges : PremetricTheory.isLimitSeq (coefficientSpace n) p result
    converges ε = PT.map
      (λ { (K , tail) → K , λ k late i →
        subst (lookup i (p k) ∼ℂ[ ε ]_) (sym (lookup-result i)) (tail k late i) })
      (finite-tail n (λ i k → lookup i (p k) ∼ℂ[ ε ] fst (coordinateLimit i))
        (λ i → snd (coordinateLimit i) ε))
