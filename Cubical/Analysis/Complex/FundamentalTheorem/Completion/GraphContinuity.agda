open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.GraphContinuity (n : ℕ) where

-- Both graph projections have constructed whole local moduli. In
-- particular the coefficient projection is injective: two completed
-- multisets representing the same coefficients agree at every radius.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Vec using (Vec; map)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootMatching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n

root-halfTriangle : ∀ x y z ε → x R.near[ ε /2₊ ] y → y R.near[ ε /2₊ ] z → x R.near[ ε ] z
root-halfTriangle x y z ε xy yz = R.subst≈ x z (1/2∈ℚ./2+/2≡id (fst ε))
  (R.isTriangular≈ x y z (ε /2₊) (ε /2₊) xy yz)

root-threeParts : ∀ x y z w ε →
  x R.near[ (ε /2₊) /2₊ ] y → y R.near[ (ε /2₊) /2₊ ] z →
  z R.near[ (ε /2₊) /2₊ ] w → x R.near[ ε ] w
root-threeParts x y z w ε xy yz zw = root-halfTriangle x z w ε
  (root-halfTriangle x y z (ε /2₊) xy yz)
  (R.isMonotone≈< z w ((ε /2₊) /2₊) (ε /2₊) (/2₊<id (ε /2₊)) zw)

FactorGraphModulus : R.Carrier → (ℚ₊ → ℚ₊) → Type₀
FactorGraphModulus x μ = ∀ ε y p q → Joint x p → Joint y q →
  x R.near[ μ ε ] y → CoefficientCloseness p ε q

opaque
  joint-factor-continuity : ∀ x → PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorGraphModulus x μ ∥₁
  joint-factor-continuity x = PT.map withCentered (factor-centered x)
    where
    withCentered : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorCenteredAt x μ) →
      Σ[ ν ∈ (ℚ₊ → ℚ₊) ] FactorGraphModulus x ν
    withCentered (μ , centered) = ν , preserve
      where
      small ν : ℚ₊ → ℚ₊
      small ε = (ε /2₊) /2₊
      ν ε = (μ (small ε) /2₊) /2₊

      preserve : FactorGraphModulus x ν
      preserve ε y p q xp yq xy = PT.rec2 (coefficientCloseness-prop p q ε)
        (λ { (rs , near-r , factor-r) (ss , near-s , factor-s) →
          coefficientCloseness-threeParts p (gaussianFactors rs) (gaussianFactors ss) q ε
            (coefficientCloseness-sym (gaussianFactors rs) p (small ε) factor-r)
            (centered (small ε) rs ss
              (R.isMonotone≈< (R.insert rs) x (μ (small ε) /2₊) (μ (small ε)) (/2₊<id (μ (small ε)))
                (R.isMonotone≈< (R.insert rs) x (ν ε) (μ (small ε) /2₊)
                  (/2₊<id (μ (small ε) /2₊)) near-r))
              (R.isMonotone≈< (R.insert ss) x (μ (small ε) /2₊) (μ (small ε)) (/2₊<id (μ (small ε)))
                (root-halfTriangle (R.insert ss) y x (μ (small ε) /2₊) near-s (R.isSym≈ x y (ν ε) xy))))
            factor-s })
        (xp (ν ε) (small ε)) (yq (ν ε) (small ε))

RootGraphModulus : MonicPolynomial n → (ℚ₊ → ℚ₊) → Type₀
RootGraphModulus p μ = ∀ ε x y q → Joint x p → Joint y q →
  CoefficientCloseness p (μ ε) q → x R.near[ ε ] y

rootGraphRadius : ℚ₊ → ℚ₊ → ℚ₊
rootGraphRadius A ε = min₊ 1
  ((rootMatchingModulus n ((A +₊ (1 +₊ 1)) +₊ (1 +₊ 1)) ((ε /2₊) /2₊) /2₊) /2₊)

opaque
  joint-root-estimate : ∀ p A → CoefficientsBounded p A → RootGraphModulus p (rootGraphRadius A)
  joint-root-estimate p A bounded = preserve
    where
    A′ A″ : ℚ₊
    A′ = A +₊ (1 +₊ 1)
    A″ = A′ +₊ (1 +₊ 1)

    small tolerance μ : ℚ₊ → ℚ₊
    small ε = (ε /2₊) /2₊
    tolerance ε = rootMatchingModulus n A″ (small ε)
    μ ε = min₊ 1 ((tolerance ε /2₊) /2₊)

    preserve : RootGraphModulus p μ
    preserve ε x y q xp yq pq = PT.rec2 (R.isProp≈ x y ε) compare
      (xp (small ε) (μ ε)) (yq (small ε) (μ ε))
      where
      compare :
        (Σ[ rs ∈ Vec GaussianRational n ] (R.insert rs R.near[ small ε ] x) ×
          CoefficientCloseness (gaussianFactors rs) (μ ε) p) →
        (Σ[ ss ∈ Vec GaussianRational n ] (R.insert ss R.near[ small ε ] y) ×
          CoefficientCloseness (gaussianFactors ss) (μ ε) q) → x R.near[ ε ] y
      compare (rs , near-r , factor-r) (ss , near-s , factor-s) =
        root-threeParts x (R.insert rs) (R.insert ss) y ε
          (R.isSym≈ (R.insert rs) x (small ε) near-r)
          (matching→inserted rs ss (small ε)
            (rootMatchingEstimate n A″ (small ε) (map gaussianℂ rs) (map gaussianℂ ss)
              (coefficientNorm-monotone (gaussianFactors rs) ⟦ A′ ⟧₊ ⟦ A″ ⟧₊
                (radius-sumL A′ (1 +₊ 1))
                (nearbyCoefficient-bound p (gaussianFactors rs) A bounded
                  (coefficientCloseness-monotone p (gaussianFactors rs) (μ ε) 1
                    (min₊≤L 1 ((tolerance ε /2₊) /2₊))
                    (coefficientCloseness-sym (gaussianFactors rs) p (μ ε) factor-r))))
              (nearbyCoefficient-bound q (gaussianFactors ss) A′
                (nearbyCoefficient-bound p q A bounded
                  (coefficientCloseness-monotone p q (μ ε) 1 (min₊≤L 1 ((tolerance ε /2₊) /2₊)) pq))
                (coefficientCloseness-monotone q (gaussianFactors ss) (μ ε) 1
                  (min₊≤L 1 ((tolerance ε /2₊) /2₊))
                  (coefficientCloseness-sym (gaussianFactors ss) q (μ ε) factor-s)))
              (coefficientCloseness-threeParts (gaussianFactors rs) p q (gaussianFactors ss) (tolerance ε)
                (coefficientCloseness-monotone (gaussianFactors rs) p (μ ε) ((tolerance ε /2₊) /2₊)
                  (min₊≤R 1 ((tolerance ε /2₊) /2₊)) factor-r)
                (coefficientCloseness-monotone p q (μ ε) ((tolerance ε /2₊) /2₊)
                  (min₊≤R 1 ((tolerance ε /2₊) /2₊)) pq)
                (coefficientCloseness-monotone q (gaussianFactors ss) (μ ε) ((tolerance ε /2₊) /2₊)
                  (min₊≤R 1 ((tolerance ε /2₊) /2₊))
                  (coefficientCloseness-sym (gaussianFactors ss) q (μ ε) factor-s))))) near-s

  joint-root-continuity : ∀ p → PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] RootGraphModulus p μ ∥₁
  joint-root-continuity p = PT.map
    (λ { (A , bounded) → rootGraphRadius A , joint-root-estimate p A bounded })
    (coefficientBound-exists p)

  joint-roots-unique : ∀ x y p → Joint x p → Joint y p → x ≡ y
  joint-roots-unique x y p xp yp = R.isSeparated≈ x y λ ε →
    PT.rec (R.isProp≈ x y ε)
      (λ { (μ , preserve) → preserve ε x y p xp yp (coefficientCloseness-refl p (μ ε)) })
      (joint-root-continuity p)
