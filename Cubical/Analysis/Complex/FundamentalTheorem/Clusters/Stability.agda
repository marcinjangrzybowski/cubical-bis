module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Stability where

-- The spectral certificates are open in coefficient space. Their tests
-- are nonvacuous by approximate FTA, including polynomials which have not
-- been factored into actual native roots.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (zero)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters
open import Cubical.Analysis.Complex.FundamentalTheorem.Approximate
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Geometry

spectrumDiameter-monotone : ∀ {n} (p : MonicPolynomial n) ε η → ε ≤₊ η →
  SpectrumDiameterBelow p ε → SpectrumDiameterBelow p η
spectrumDiameter-monotone p ε η below = PT.map λ { (δ , bounded) → δ ,
  λ roots accurate i j → <≤ℝ-trans (distanceℂ (lookup i roots) (lookup j roots)) ⟦ ε ⟧₊ ⟦ η ⟧₊
    (bounded roots accurate i j) (radius-monotone ε η below) }

spectrumDiameter-open : ∀ {n} (p : MonicPolynomial n) ε → SpectrumDiameterBelow p ε →
  PT.∥ Σ[ δ ∈ ℚ₊ ] (∀ q → CoefficientCloseness p δ q → SpectrumDiameterBelow q ε) ∥₁
spectrumDiameter-open p ε = PT.map λ { (δ , bounded) → δ /2₊ ,
  λ q close → PT.∣ δ /2₊ , (λ roots accurate → bounded roots
    (coefficientCloseness-halfTriangle p q (linearFactors roots) δ close accurate)) ∣₁ }

spectraSeparated-open : ∀ {m n} (p : MonicPolynomial m) (q : MonicPolynomial n) →
  SpectraSeparated p q → PT.∥ Σ[ δ ∈ ℚ₊ ] (∀ p′ q′ →
    CoefficientCloseness p δ p′ → CoefficientCloseness q δ q′ → SpectraSeparated p′ q′) ∥₁
spectraSeparated-open p q = PT.map λ { (gap , δ , separated) → δ /2₊ ,
  λ p′ q′ close-p close-q → PT.∣ gap , δ /2₊ , (λ roots roots′ accurate accurate′ →
    separated roots roots′
      (coefficientCloseness-halfTriangle p p′ (linearFactors roots) δ close-p accurate)
      (coefficientCloseness-halfTriangle q q′ (linearFactors roots′) δ close-q accurate′)) ∣₁ }

spectraSeparated-sym : ∀ {m n} (p : MonicPolynomial m) (q : MonicPolynomial n) →
  SpectraSeparated p q → SpectraSeparated q p
spectraSeparated-sym p q = PT.map λ { (gap , δ , separated) → gap , δ ,
  λ roots roots′ accurate accurate′ i j → subst (⟦ gap ⟧₊ ≤ℝ_)
    (distanceℂ-sym (lookup j roots′) (lookup i roots))
    (separated roots′ roots accurate′ accurate j i) }

spectrumDiameter-nonvacuous : ∀ {n} (p : MonicPolynomial n) ε → SpectrumDiameterBelow p ε →
  PT.∥ Σ[ roots ∈ Vec ℂ n ] ConfigurationDiameterBelow roots ε ∥₁
spectrumDiameter-nonvacuous {n} p ε = PT.rec PT.isPropPropTrunc λ { (δ , bounded) →
  PT.map (λ { (roots , accurate) → roots , bounded roots accurate })
    (approximateFundamentalTheorem n p δ) }

spectraSeparated-nonvacuous : ∀ {m n} (p : MonicPolynomial m) (q : MonicPolynomial n) →
  SpectraSeparated p q → PT.∥ Σ[ gap ∈ ℚ₊ ] Σ[ roots ∈ Vec ℂ m ] Σ[ roots′ ∈ Vec ℂ n ]
    ConfigurationGap roots roots′ gap ∥₁
spectraSeparated-nonvacuous {m} {n} p q = PT.rec PT.isPropPropTrunc λ { (gap , δ , separated) →
  PT.map2 (λ { (roots , accurate) (roots′ , accurate′) →
    gap , roots , roots′ , separated roots roots′ accurate accurate′ })
    (approximateFundamentalTheorem m p δ) (approximateFundamentalTheorem n q δ) }

-- Positive degree is essential: the degree-zero spectrum is empty.
spectraSeparated-irreflexive : ∀ {n} (p : MonicPolynomial (suc n)) → SpectraSeparated p p → Empty.⊥
spectraSeparated-irreflexive {n} p = PT.rec Empty.isProp⊥ λ { (gap , δ , separated) →
  PT.rec Empty.isProp⊥ (λ { (roots , accurate) →
    <ℝ→≰ 0ℝ ⟦ gap ⟧₊ (radius-positive gap)
      (subst (⟦ gap ⟧₊ ≤ℝ_) (distanceℂ-refl (lookup zero roots))
        (separated roots roots accurate accurate zero zero)) })
    (approximateFundamentalTheorem (suc n) p δ) }
