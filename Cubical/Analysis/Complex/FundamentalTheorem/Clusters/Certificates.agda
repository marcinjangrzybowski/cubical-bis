module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Certificates where

-- A sufficiently accurate finite configuration with a strict margin
-- certifies the catalogue's spectrum predicates. The result quantifies
-- over ALL sufficiently accurate factorizations, not just this witness.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Geometry
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Matching

diameter-from-approximation : ∀ {n} (p : MonicPolynomial n) μ → FactorMatchingAt p μ →
  ∀ ε η (centers : Vec ℂ n) →
  (∀ i j → distanceℂ (lookup i centers) (lookup j centers) + ⟦ η ⟧₊ ≤ℝ ⟦ ε ⟧₊) →
  CoefficientCloseness p (μ ((η /2₊) /2₊)) (linearFactors centers) → SpectrumDiameterBelow p ε
diameter-from-approximation p μ matching ε η centers margin accurate =
  PT.∣ μ ((η /2₊) /2₊) , (λ roots close → matching-diameter centers roots ε η margin
    (matching ((η /2₊) /2₊) roots centers close accurate)) ∣₁

separation-from-approximations : ∀ {m n} (p : MonicPolynomial m) (q : MonicPolynomial n) μ ν →
  FactorMatchingAt p μ → FactorMatchingAt q ν →
  ∀ gap η (centers : Vec ℂ m) (centers′ : Vec ℂ n) →
  (∀ i j → ⟦ gap ⟧₊ + ⟦ η ⟧₊ ≤ℝ distanceℂ (lookup i centers) (lookup j centers′)) →
  CoefficientCloseness p (μ ((η /2₊) /2₊)) (linearFactors centers) →
  CoefficientCloseness q (ν ((η /2₊) /2₊)) (linearFactors centers′) → SpectraSeparated p q
separation-from-approximations p q μ ν match-p match-q gap η centers centers′ margin first second =
  PT.∣ gap , δ , (λ roots roots′ close close′ → matching-gap centers centers′ gap η margin roots roots′
    (match-p ρ roots centers
      (coefficientCloseness-monotone p (linearFactors roots) δ (μ ρ) (min₊≤L (μ ρ) (ν ρ)) close) first)
    (match-q ρ roots′ centers′
      (coefficientCloseness-monotone q (linearFactors roots′) δ (ν ρ) (min₊≤R (μ ρ) (ν ρ)) close′) second)) ∣₁
  where
  ρ δ : ℚ₊
  ρ = (η /2₊) /2₊
  δ = min₊ (μ ρ) (ν ρ)

finite-diameter→spectrum : ∀ {n} (roots : Vec ℂ n) ε →
  ConfigurationDiameterBelow roots ε → SpectrumDiameterBelow (linearFactors roots) ε
finite-diameter→spectrum roots ε small = PT.rec2 PT.isPropPropTrunc
  (λ { (η , margin) (μ , matching) → diameter-from-approximation (linearFactors roots) μ matching
    ε η roots margin (coefficientCloseness-refl (linearFactors roots) (μ ((η /2₊) /2₊))) })
  (diameter-margin roots ε small) (factorMatchingAt (linearFactors roots))

spectrum→finite-diameter : ∀ {n} (roots : Vec ℂ n) ε →
  SpectrumDiameterBelow (linearFactors roots) ε → ConfigurationDiameterBelow roots ε
spectrum→finite-diameter roots ε = PT.rec
  (isPropΠ2 λ i j → isProp<ℝ (distanceℂ (lookup i roots) (lookup j roots)) ⟦ ε ⟧₊)
  λ { (δ , bounded) → bounded roots (coefficientCloseness-refl (linearFactors roots) δ) }

finite-gap→spectra : ∀ {m n} (roots : Vec ℂ m) (roots′ : Vec ℂ n) gap →
  ConfigurationGap roots roots′ gap → SpectraSeparated (linearFactors roots) (linearFactors roots′)
finite-gap→spectra roots roots′ gap separated = PT.rec2 PT.isPropPropTrunc
  (λ { (μ , first) (ν , second) → separation-from-approximations
    (linearFactors roots) (linearFactors roots′) μ ν first second
    (gap /2₊) (gap /2₊) roots roots′
    (λ i j → subst (_≤ℝ distanceℂ (lookup i roots) (lookup j roots′))
      (sym (rat+rat (fst (gap /2₊)) (fst (gap /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst gap))))
      (separated i j))
    (coefficientCloseness-refl (linearFactors roots) (μ (((gap /2₊) /2₊) /2₊)))
    (coefficientCloseness-refl (linearFactors roots′) (ν (((gap /2₊) /2₊) /2₊))) })
  (factorMatchingAt (linearFactors roots)) (factorMatchingAt (linearFactors roots′))

spectra→finite-gap : ∀ {m n} (roots : Vec ℂ m) (roots′ : Vec ℂ n) →
  SpectraSeparated (linearFactors roots) (linearFactors roots′) →
  PT.∥ Σ[ gap ∈ ℚ₊ ] ConfigurationGap roots roots′ gap ∥₁
spectra→finite-gap roots roots′ = PT.map λ { (gap , δ , separated) → gap ,
  separated roots roots′ (coefficientCloseness-refl (linearFactors roots) δ)
    (coefficientCloseness-refl (linearFactors roots′) δ) }

finite-apart→spectra : ∀ {m n} (roots : Vec ℂ m) (roots′ : Vec ℂ n) →
  (∀ i j → 0ℝ <ℝ distanceℂ (lookup i roots) (lookup j roots′)) →
  SpectraSeparated (linearFactors roots) (linearFactors roots′)
finite-apart→spectra roots roots′ apart = PT.rec PT.isPropPropTrunc
  (λ { (gap , separated) → finite-gap→spectra roots roots′ gap separated })
  (apart-configurations-gap roots roots′ apart)
