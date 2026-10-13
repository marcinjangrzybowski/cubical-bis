module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.RootContainment where

-- A prescribed small-residual point can be retained as the first factor.
-- Approximate FTA is applied only to its synthetic quotient. This connects
-- the finite spectral tests with actual roots, without extracting roots
-- from a completed multiset or selecting an infinite family.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (zero)
open import Cubical.Data.Vec using (Vec; _∷_)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic.Continuity
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters
open import Cubical.Analysis.Complex.FundamentalTheorem.Approximate
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale

approximateFactors-at-small-residual : ∀ {n} (p : MonicPolynomial (suc n)) z ε →
  evaluateMonic p z ∼ℂ[ ε /2₊ ] 0ℂ →
  PT.∥ Σ[ roots ∈ Vec ℂ n ] CoefficientCloseness p ε (linearFactors (z ∷ roots)) ∥₁
approximateFactors-at-small-residual {n} p z ε small = PT.rec PT.isPropPropTrunc
  (λ { (δ , continuous) → PT.map (λ { (roots , accurate) → roots ,
    coefficientCloseness-halfTriangle p (multiplyLinear z quotient) (linearFactors (z ∷ roots)) ε
      remainder-close (continuous (linearFactors roots) accurate) })
    (approximateFundamentalTheorem n quotient δ) })
  (multiplyLinear-coefficientContinuous z quotient (ε /2₊))
  where
  quotient : MonicPolynomial n
  quotient = quotientMonic p z

  remainder-close : CoefficientCloseness p (ε /2₊) (multiplyLinear z quotient)
  remainder-close = subst (λ q → CoefficientCloseness q (ε /2₊) (multiplyLinear z quotient))
    (sym (reconstructMonic p z))
    (addConstant-small (evaluateMonic p z) (multiplyLinear z quotient) (ε /2₊) small)

approximateFactors-containing-root : ∀ {n} (p : MonicPolynomial (suc n)) z →
  evaluateMonic p z ≡ 0ℂ → ∀ ε →
  PT.∥ Σ[ roots ∈ Vec ℂ n ] CoefficientCloseness p ε (linearFactors (z ∷ roots)) ∥₁
approximateFactors-containing-root p z root ε = approximateFactors-at-small-residual p z ε
  (subst (λ value → value ∼ℂ[ ε /2₊ ] 0ℂ) (sym root) (refl∼ℂ 0ℂ (ε /2₊)))

spectraSeparated-root-gap : ∀ {m n} (p : MonicPolynomial (suc m)) (q : MonicPolynomial (suc n)) →
  SpectraSeparated p q → PT.∥ Σ[ gap ∈ ℚ₊ ] (∀ z w →
    evaluateMonic p z ≡ 0ℂ → evaluateMonic q w ≡ 0ℂ → ⟦ gap ⟧₊ ≤ℝ distanceℂ z w) ∥₁
spectraSeparated-root-gap p q = PT.map λ { (gap , δ , separated) → gap ,
  λ z w root root′ → PT.rec2 (isProp≤ℝ ⟦ gap ⟧₊ (distanceℂ z w))
    (λ { (roots , accurate) (roots′ , accurate′) →
      separated (z ∷ roots) (w ∷ roots′) accurate accurate′ zero zero })
    (approximateFactors-containing-root p z root δ)
    (approximateFactors-containing-root q w root′ δ) }

spectraSeparated-no-common-root : ∀ {m n} (p : MonicPolynomial (suc m)) (q : MonicPolynomial (suc n)) →
  SpectraSeparated p q → ∀ z → evaluateMonic p z ≡ 0ℂ → evaluateMonic q z ≡ 0ℂ → Empty.⊥
spectraSeparated-no-common-root p q separated z root root′ = PT.rec Empty.isProp⊥
  (λ { (gap , bounded) → <ℝ→≰ 0ℝ ⟦ gap ⟧₊ (radius-positive gap)
    (subst (⟦ gap ⟧₊ ≤ℝ_) (distanceℂ-refl z) (bounded z z root root′)) })
  (spectraSeparated-root-gap p q separated)
