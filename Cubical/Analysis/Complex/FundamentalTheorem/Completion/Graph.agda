open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph (n : ℕ) where

-- The closed graph relates completed configurations to native coefficient
-- vectors by arbitrarily accurate joint finite approximations. This is a
-- proposition and does not choose an approximation sequence.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (max)
import Cubical.Data.Nat.Order as N
open import Cubical.Data.Vec using (Vec)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n

private
  module RT = PremetricTheory R.space
  module CT = PremetricTheory (coefficientSpace n)

Joint : R.Carrier → MonicPolynomial n → Type₀
Joint x p = ∀ α β → PT.∥ Σ[ qs ∈ Vec GaussianRational n ]
  (R.insert qs R.near[ α ] x) × CoefficientCloseness (gaussianFactors qs) β p ∥₁

isPropJoint : ∀ x p → isProp (Joint x p)
isPropJoint x p = isPropΠ2 λ _ _ → PT.isPropPropTrunc

joint-insert : ∀ qs → Joint (R.insert qs) (gaussianFactors qs)
joint-insert qs α β = PT.∣ qs , R.isRefl≈ (R.insert qs) α , coefficientCloseness-refl (gaussianFactors qs) β ∣₁

opaque
  joint-coefficients-unique : ∀ x p q → Joint x p → Joint x q → p ≡ q
  joint-coefficients-unique x p q xp xq = coefficientCloseness-separated p q λ ε →
    PT.rec (coefficientCloseness-prop p q ε) (withModulus ε) (factor-centered x)
    where
    withModulus : ∀ ε → (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorCenteredAt x μ) → CoefficientCloseness p ε q
    withModulus ε (μ , centered) = PT.rec2 (coefficientCloseness-prop p q ε)
      (λ { (rs , near-r , factor-r) (ss , near-s , factor-s) →
        coefficientCloseness-threeParts p (gaussianFactors rs) (gaussianFactors ss) q ε
          (coefficientCloseness-sym (gaussianFactors rs) p small factor-r)
          (centered small rs ss near-r near-s) factor-s })
      (xp (μ small) small) (xq (μ small) small)
      where
      small : ℚ₊
      small = (ε /2₊) /2₊

FactorFiber : R.Carrier → Type₀
FactorFiber x = Σ[ p ∈ MonicPolynomial n ] Joint x p

isPropFactorFiber : ∀ x → isProp (FactorFiber x)
isPropFactorFiber x (p , xp) (q , xq) = Σ≡Prop (isPropJoint x) (joint-coefficients-unique x p q xp xq)

opaque
  joint-limit : ∀ (xs : ℕ → R.Carrier) (ps : ℕ → MonicPolynomial n) x p →
    (∀ k → Joint (xs k) (ps k)) → RT.isLimitSeq xs x → CT.isLimitSeq ps p → Joint x p
  joint-limit xs ps x p joint source-limit target-limit α β = PT.rec2 PT.isPropPropTrunc
    (λ { (K , source-tail) (L , target-tail) → PT.map
      (λ { (qs , near , factor) → qs ,
        R.subst≈ (R.insert qs) x (1/2∈ℚ./2+/2≡id (fst α))
          (R.isTriangular≈ (R.insert qs) (xs (max K L)) x (α /2₊) (α /2₊) near
            (source-tail (max K L) (N.left-≤-max {m = K} {n = L}))) ,
        coefficientCloseness-halfTriangle (gaussianFactors qs) (ps (max K L)) p β factor
          (target-tail (max K L) (N.right-≤-max {n = L} {m = K})) })
      (joint (max K L) (α /2₊) (β /2₊)) })
    (source-limit (α /2₊)) (target-limit (β /2₊))
